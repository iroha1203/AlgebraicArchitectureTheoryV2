//! `shigure partial` の論理式・開領域の静的意味検査（Phase 5 / AC2）。

use super::ast_phase5_obs::*;
use super::check::{CResult, check_coeff_domain};
use super::check_phase4_lift_artin::p4_type_err;
use crate::law::ast::Span;
use crate::law::check::{duplicate, reference};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::json::InputError;
use std::collections::{HashMap, HashSet};

const RED_ZONE: usize = 128 * 1024;
const STACK_STEP: usize = 4 * 1024 * 1024;

pub(super) struct FormulaCheckScope<'a> {
    pub(super) op_arities: &'a HashMap<String, usize>,
    pub(super) rel_arities: &'a HashMap<String, usize>,
    pub(super) sorts: &'a HashMap<String, HashSet<String>>,
    pub(super) slots: &'a HashSet<String>,
    pub(super) allow_arbitrary_refs: bool,
}

fn check_p5_term<E: InputError>(
    raw: &RawPartialTerm,
    scope: &FormulaCheckScope<'_>,
    bound_vars: &HashSet<&str>,
    control: &Control,
) -> CResult<ShigurePartialTerm, E> {
    stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        match raw {
            RawPartialTerm::IdentOrConst(id) => {
                if bound_vars.contains(id.name.as_str()) {
                    Ok(ShigurePartialTerm::Var(id.name.clone()))
                } else {
                    Ok(ShigurePartialTerm::Const(id.name.clone()))
                }
            }
            RawPartialTerm::ConstLit(c, span) | RawPartialTerm::ExplicitConst(c, span) => {
                if c.trim().is_empty() {
                    return p4_type_err(*span, "empty constant in partial formula term");
                }
                Ok(ShigurePartialTerm::Const(c.clone()))
            }
            RawPartialTerm::Slot(s) => {
                if !scope.allow_arbitrary_refs && !scope.slots.contains(&s.name) {
                    return reference(s.span, format!("unknown slot `{}` in partial term", s.name));
                }
                Ok(ShigurePartialTerm::Slot(s.name.clone()))
            }
            RawPartialTerm::App {
                op_name,
                args,
                span,
            } => {
                if !scope.allow_arbitrary_refs {
                    let Some(&arity) = scope.op_arities.get(&op_name.name) else {
                        return reference(
                            op_name.span,
                            format!("unknown operation `{}` in partial term", op_name.name),
                        );
                    };
                    if args.len() != arity {
                        return p4_type_err(
                            *span,
                            format!(
                                "operation `{}` expects {arity} args, got {}",
                                op_name.name,
                                args.len()
                            ),
                        );
                    }
                }
                let mut checked_args = Vec::with_capacity(args.len());
                for a in args {
                    checked_args.push(check_p5_term(a, scope, bound_vars, control)?);
                }
                Ok(ShigurePartialTerm::App {
                    op_name: op_name.name.clone(),
                    args: checked_args,
                })
            }
            RawPartialTerm::Let {
                var, bound, body, ..
            } => {
                let checked_bound = check_p5_term(bound, scope, bound_vars, control)?;
                let mut next = bound_vars.clone();
                next.insert(var.name.as_str());
                let checked_body = check_p5_term(body, scope, &next, control)?;
                Ok(ShigurePartialTerm::Let {
                    var: var.name.clone(),
                    bound: Box::new(checked_bound),
                    body: Box::new(checked_body),
                })
            }
            RawPartialTerm::BinOp { op, lhs, rhs, .. } => {
                let l = check_p5_term(lhs, scope, bound_vars, control)?;
                let r = check_p5_term(rhs, scope, bound_vars, control)?;
                Ok(ShigurePartialTerm::BinOp {
                    op: *op,
                    lhs: Box::new(l),
                    rhs: Box::new(r),
                })
            }
        }
    })
}

fn check_p5_formula<E: InputError>(
    raw: &RawPartialFormula,
    scope: &FormulaCheckScope<'_>,
    bound_vars: &HashSet<&str>,
    control: &Control,
) -> CResult<ShigurePartialFormula, E> {
    stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        match raw {
            RawPartialFormula::Eq(a, b, _) => Ok(ShigurePartialFormula::Eq(
                check_p5_term(a, scope, bound_vars, control)?,
                check_p5_term(b, scope, bound_vars, control)?,
            )),
            RawPartialFormula::Rel {
                rel_name,
                args,
                span,
            } => {
                if !scope.allow_arbitrary_refs {
                    let Some(&arity) = scope.rel_arities.get(&rel_name.name) else {
                        return reference(
                            rel_name.span,
                            format!("unknown relation `{}` in partial formula", rel_name.name),
                        );
                    };
                    if args.len() != arity {
                        return p4_type_err(
                            *span,
                            format!(
                                "relation `{}` expects {arity} args, got {}",
                                rel_name.name,
                                args.len()
                            ),
                        );
                    }
                }
                let mut checked_args = Vec::with_capacity(args.len());
                for a in args {
                    checked_args.push(check_p5_term(a, scope, bound_vars, control)?);
                }
                Ok(ShigurePartialFormula::Rel {
                    rel_name: rel_name.name.clone(),
                    args: checked_args,
                })
            }
            RawPartialFormula::Graph {
                op_name,
                args,
                output,
                span,
            } => {
                if !scope.allow_arbitrary_refs {
                    let Some(&arity) = scope.op_arities.get(&op_name.name) else {
                        return reference(
                            op_name.span,
                            format!("unknown operation `{}` in graph()", op_name.name),
                        );
                    };
                    if args.len() != arity {
                        return p4_type_err(
                            *span,
                            format!(
                                "operation `{}` expects {arity} args, got {}",
                                op_name.name,
                                args.len()
                            ),
                        );
                    }
                }
                let mut checked_args = Vec::with_capacity(args.len());
                for a in args {
                    checked_args.push(check_p5_term(a, scope, bound_vars, control)?);
                }
                let checked_out = check_p5_term(output, scope, bound_vars, control)?;
                Ok(ShigurePartialFormula::Graph {
                    op_name: op_name.name.clone(),
                    args: checked_args,
                    output: checked_out,
                })
            }
            RawPartialFormula::Defined {
                op_name,
                args,
                span,
            } => {
                if !scope.allow_arbitrary_refs {
                    let Some(&arity) = scope.op_arities.get(&op_name.name) else {
                        return reference(
                            op_name.span,
                            format!("unknown operation `{}` in defined()", op_name.name),
                        );
                    };
                    if args.len() != arity {
                        return p4_type_err(
                            *span,
                            format!(
                                "operation `{}` expects {arity} args, got {}",
                                op_name.name,
                                args.len()
                            ),
                        );
                    }
                }
                let mut checked_args = Vec::with_capacity(args.len());
                for a in args {
                    checked_args.push(check_p5_term(a, scope, bound_vars, control)?);
                }
                Ok(ShigurePartialFormula::Defined {
                    op_name: op_name.name.clone(),
                    args: checked_args,
                })
            }
            RawPartialFormula::Not(inner, _) => Ok(ShigurePartialFormula::Not(Box::new(
                check_p5_formula(inner, scope, bound_vars, control)?,
            ))),
            RawPartialFormula::And(list, _) => {
                let mut out = Vec::with_capacity(list.len());
                for f in list {
                    out.push(check_p5_formula(f, scope, bound_vars, control)?);
                }
                Ok(ShigurePartialFormula::And(out))
            }
            RawPartialFormula::Or(list, _) => {
                let mut out = Vec::with_capacity(list.len());
                for f in list {
                    out.push(check_p5_formula(f, scope, bound_vars, control)?);
                }
                Ok(ShigurePartialFormula::Or(out))
            }
            RawPartialFormula::Exists {
                var,
                sort,
                restricted_domain,
                body,
                ..
            } => {
                let dom = check_quant_sort(sort, restricted_domain.as_deref(), scope)?;
                let mut next = bound_vars.clone();
                next.insert(var.name.as_str());
                Ok(ShigurePartialFormula::Exists {
                    var: var.name.clone(),
                    sort: sort.name.clone(),
                    restricted_domain: dom,
                    body: Box::new(check_p5_formula(body, scope, &next, control)?),
                })
            }
            RawPartialFormula::Forall {
                var,
                sort,
                restricted_domain,
                body,
                ..
            } => {
                let dom = check_quant_sort(sort, restricted_domain.as_deref(), scope)?;
                let mut next = bound_vars.clone();
                next.insert(var.name.as_str());
                Ok(ShigurePartialFormula::Forall {
                    var: var.name.clone(),
                    sort: sort.name.clone(),
                    restricted_domain: dom,
                    body: Box::new(check_p5_formula(body, scope, &next, control)?),
                })
            }
        }
    })
}

fn check_quant_sort<E: InputError>(
    sort: &crate::law::ast::Ident,
    restricted_domain: Option<&[(String, Span)]>,
    scope: &FormulaCheckScope<'_>,
) -> CResult<Option<Vec<String>>, E> {
    let elems_opt = scope.sorts.get(&sort.name);
    if !scope.allow_arbitrary_refs && elems_opt.is_none() {
        return reference(
            sort.span,
            format!("unknown sort `{}` in quantifier", sort.name),
        );
    }
    let Some(dom) = restricted_domain else {
        return Ok(None);
    };
    let mut out = Vec::with_capacity(dom.len());
    for (elem, span) in dom {
        if let Some(elems) = elems_opt
            && !elems.contains(elem)
        {
            return reference(
                *span,
                format!(
                    "unknown element `{elem}` in restricted domain of sort `{}`",
                    sort.name
                ),
            );
        }
        out.push(elem.clone());
    }
    Ok(Some(out))
}

pub(super) fn check_eval_law<E: InputError>(
    raw: &RawPartialEvalLaw,
    scope: &FormulaCheckScope<'_>,
    control: &Control,
) -> CResult<ShigurePartialEvalLaw, E> {
    let empty_bound = HashSet::new();
    let antecedent = match &raw.antecedent {
        Some(a) => Some(check_p5_formula(a, scope, &empty_bound, control)?),
        None => None,
    };
    let conclusion = check_p5_formula(&raw.conclusion, scope, &empty_bound, control)?;
    Ok(ShigurePartialEvalLaw {
        name: raw.name.name.clone(),
        antecedent,
        conclusion,
        is_required_law: raw.is_required_law,
        span: raw.span,
    })
}

struct CheckedOpenSide {
    sort_list: Vec<(String, Vec<String>)>,
    sort_map: HashMap<String, HashSet<String>>,
    ops: Vec<ShigureOpenOpTable>,
    op_arities: HashMap<String, usize>,
    rels: Vec<ShigureOpenRelTable>,
    rel_arities: HashMap<String, usize>,
}

fn check_open_side<E: InputError>(
    sorts: &[RawSortDef],
    ops: &[RawOpenOpTable],
    rels: &[RawOpenRelTable],
) -> CResult<CheckedOpenSide, E> {
    let mut sort_map: HashMap<String, HashSet<String>> = HashMap::new();
    let mut sort_list = Vec::with_capacity(sorts.len());
    for (s, elems, _) in sorts {
        if sort_map.contains_key(&s.name) {
            return duplicate(s.span, format!("duplicate open_domain sort `{}`", s.name));
        }
        let mut set = HashSet::new();
        let mut vec = Vec::with_capacity(elems.len());
        for (e, e_span) in elems {
            if !set.insert(e.clone()) {
                return duplicate(*e_span, format!("duplicate element `{e}`"));
            }
            vec.push(e.clone());
        }
        sort_map.insert(s.name.clone(), set);
        sort_list.push((s.name.clone(), vec));
    }
    let mut checked_ops = Vec::with_capacity(ops.len());
    let mut op_arities = HashMap::new();
    for op in ops {
        if op_arities.contains_key(&op.name.name) {
            return duplicate(
                op.name.span,
                format!("duplicate op_table `{}`", op.name.name),
            );
        }
        let mut arg_sorts = Vec::with_capacity(op.arg_sorts.len());
        for a in &op.arg_sorts {
            if !sort_map.contains_key(&a.name) {
                return reference(a.span, format!("unknown sort `{}`", a.name));
            }
            arg_sorts.push(a.name.clone());
        }
        if !sort_map.contains_key(&op.out_sort.name) {
            return reference(
                op.out_sort.span,
                format!("unknown sort `{}`", op.out_sort.name),
            );
        }
        let mut entries = Vec::with_capacity(op.entries.len());
        for (args, out_opt, e_span) in &op.entries {
            if args.len() != arg_sorts.len() {
                return p4_type_err(*e_span, "open_domain op_table entry arity mismatch");
            }
            let mut checked_args = Vec::with_capacity(args.len());
            for (s, (a, a_span)) in arg_sorts.iter().zip(args) {
                if !sort_map[s].contains(a) {
                    return reference(*a_span, format!("unknown element `{a}` of sort `{s}`"));
                }
                checked_args.push(a.clone());
            }
            let checked_out = match out_opt {
                Some((o, o_span)) => {
                    if !sort_map[&op.out_sort.name].contains(o) {
                        return reference(*o_span, format!("unknown output element `{o}`"));
                    }
                    Some(o.clone())
                }
                None => None,
            };
            entries.push((checked_args, checked_out));
        }
        op_arities.insert(op.name.name.clone(), arg_sorts.len());
        checked_ops.push(ShigureOpenOpTable {
            name: op.name.name.clone(),
            arg_sorts,
            out_sort: op.out_sort.name.clone(),
            entries,
        });
    }
    let mut checked_rels = Vec::with_capacity(rels.len());
    let mut rel_arities = HashMap::new();
    for rel in rels {
        if rel_arities.contains_key(&rel.name.name) {
            return duplicate(
                rel.name.span,
                format!("duplicate rel_table `{}`", rel.name.name),
            );
        }
        let mut arg_sorts = Vec::with_capacity(rel.arg_sorts.len());
        for a in &rel.arg_sorts {
            if !sort_map.contains_key(&a.name) {
                return reference(a.span, format!("unknown sort `{}`", a.name));
            }
            arg_sorts.push(a.name.clone());
        }
        let mut entries = Vec::with_capacity(rel.entries.len());
        for (args, e_span) in &rel.entries {
            if args.len() != arg_sorts.len() {
                return p4_type_err(*e_span, "open_domain rel_table entry arity mismatch");
            }
            let mut checked_args = Vec::with_capacity(args.len());
            for (s, (a, a_span)) in arg_sorts.iter().zip(args) {
                if !sort_map[s].contains(a) {
                    return reference(*a_span, format!("unknown element `{a}` of sort `{s}`"));
                }
                checked_args.push(a.clone());
            }
            entries.push(checked_args);
        }
        rel_arities.insert(rel.name.name.clone(), arg_sorts.len());
        checked_rels.push(ShigureOpenRelTable {
            name: rel.name.name.clone(),
            arg_sorts,
            entries,
        });
    }
    Ok(CheckedOpenSide {
        sort_list,
        sort_map,
        ops: checked_ops,
        op_arities,
        rels: checked_rels,
        rel_arities,
    })
}

pub(super) fn check_open_domain<E: InputError>(
    raw: &RawOpenDomain,
    control: &Control,
) -> CResult<ShigureOpenDomain, E> {
    let sub = check_open_side(
        &raw.substructure_sorts,
        &raw.substructure_ops,
        &raw.substructure_rels,
    )?;
    let amb = check_open_side(&raw.ambient_sorts, &raw.ambient_ops, &raw.ambient_rels)?;

    let mut fiber_checks = Vec::with_capacity(raw.fiber_checks.len());
    for fc in &raw.fiber_checks {
        let Some(sub_target) = sub.sort_map.get(&fc.target_sort.name) else {
            return reference(
                fc.target_sort.span,
                format!("unknown substructure sort `{}`", fc.target_sort.name),
            );
        };
        let mut known_targets = Vec::with_capacity(fc.known_targets.len());
        for (t, t_span) in &fc.known_targets {
            if !sub_target.contains(t) {
                return reference(*t_span, format!("unknown target `{t}`"));
            }
            known_targets.push(t.clone());
        }
        fiber_checks.push(ShigureFiberCoverageCheck {
            op_name: fc.op_name.name.clone(),
            arg_sort: fc.arg_sort.name.clone(),
            target_sort: fc.target_sort.name.clone(),
            known_targets,
        });
    }
    let empty_slots = HashSet::new();
    let law_scope = FormulaCheckScope {
        op_arities: &amb.op_arities,
        rel_arities: &amb.rel_arities,
        sorts: &amb.sort_map,
        slots: &empty_slots,
        allow_arbitrary_refs: false,
    };
    let positive_or_law = check_eval_law(&raw.positive_or_law, &law_scope, control)?;
    let affine_restriction = match &raw.affine_restriction {
        Some(ar) => Some(ShigureAffineRestriction {
            coeff_domain: check_coeff_domain(&ar.domain, control)?,
            m_matrix: ar.m_matrix.clone(),
            b_rhs: ar.b_rhs.clone(),
            r_matrix: ar.r_matrix.clone(),
            num_vars: ar.num_vars,
            span: ar.span,
        }),
        None => None,
    };

    Ok(ShigureOpenDomain {
        substructure_sorts: sub.sort_list,
        ambient_sorts: amb.sort_list,
        substructure_ops: sub.ops,
        ambient_ops: amb.ops,
        substructure_rels: sub.rels,
        ambient_rels: amb.rels,
        fiber_checks,
        positive_or_law,
        affine_restriction,
        span: raw.span,
    })
}
