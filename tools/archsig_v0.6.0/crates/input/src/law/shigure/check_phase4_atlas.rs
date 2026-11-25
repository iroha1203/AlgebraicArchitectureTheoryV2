//! `shigure atlas` 宣言の静的意味検査（Phase 4 / AC2）。

use super::ast_phase4_diag_atlas::*;
use super::check::{
    CResult, LiteralDomainRule, check_coeff_domain, check_poly_literals, check_poly_vars,
};
use super::check_family::check_named_polys_in_scope;
use super::check_phase4_diagnostics::check_supported_nerve;
use super::check_phase4_lift_artin::{
    check_p4_coord_scalar_map, check_p4_coord_value, check_p4_origins, check_p4_poly_assign_map,
    check_p4_unique_idents, p4_type_err,
};
use super::*;
use crate::law::ast::{Ident, Span};
use crate::law::check::{Checker, duplicate, full, reference};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::json::InputError;
use std::collections::HashSet;

#[allow(clippy::too_many_arguments)]
fn check_simple_graph<E: InputError>(
    raw_vertices: &[Ident],
    raw_edges: &[RawGraphEdge],
    coeff_domain: &ShigureCoeffDomain,
    r_idx: usize,
    checker: &Checker<'_, E>,
    span: Span,
    context: &str,
    control: &Control,
) -> CResult<(Vec<String>, Vec<ShigureGraphEdge>), E> {
    if raw_vertices.is_empty() {
        return p4_type_err(span, format!("{context} must have at least one vertex"));
    }
    if raw_edges.is_empty() {
        return p4_type_err(span, format!("{context} must have at least one edge"));
    }
    let vertices = check_p4_unique_idents(raw_vertices, "vertex", context)?;
    let v_set: HashSet<&str> = vertices.iter().map(String::as_str).collect();
    let mut e_set = HashSet::new();
    let mut undirected = HashSet::new();
    let mut edges = Vec::with_capacity(raw_edges.len());
    for e in raw_edges {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if e.name.name == "none" {
            return p4_type_err(e.name.span, "graph edge name `none` is reserved");
        }
        if !e_set.insert(e.name.name.as_str()) {
            return duplicate(
                e.name.span,
                format!("duplicate edge `{}` in {context}", e.name.name),
            );
        }
        if !v_set.contains(e.from.name.as_str()) {
            return reference(
                e.from.span,
                format!("unknown vertex `{}` in edge `{}` ({context})", e.from.name, e.name.name),
            );
        }
        if !v_set.contains(e.to.name.as_str()) {
            return reference(
                e.to.span,
                format!("unknown vertex `{}` in edge `{}` ({context})", e.to.name, e.name.name),
            );
        }
        if e.from.name == e.to.name {
            return p4_type_err(
                e.span,
                format!("simple graph forbids self-loop edge `{}` in {context}", e.name.name),
            );
        }
        let pair = if e.from.name < e.to.name {
            (e.from.name.as_str(), e.to.name.as_str())
        } else {
            (e.to.name.as_str(), e.from.name.as_str())
        };
        if !undirected.insert(pair) {
            return p4_type_err(
                e.span,
                format!(
                    "simple graph forbids parallel edges between `{}` and `{}` in {context}",
                    pair.0, pair.1
                ),
            );
        }
        let offset = check_p4_coord_value(&e.offset, coeff_domain, r_idx, checker, e.span, control)?;
        edges.push(ShigureGraphEdge {
            name: e.name.name.clone(),
            from: e.from.name.clone(),
            to: e.to.name.clone(),
            offset,
            span: e.span,
        });
    }
    Ok((vertices, edges))
}

fn check_total_arrow_map<E: InputError>(
    raw: &[(Ident, Ident, Span)],
    dom: &HashSet<&str>,
    cod: &HashSet<&str>,
    span: Span,
    kind: &str,
    context: &str,
) -> CResult<Vec<(String, String)>, E> {
    let mut seen = HashSet::new();
    let mut out = Vec::with_capacity(raw.len());
    for (lhs, rhs, _) in raw {
        if !dom.contains(lhs.name.as_str()) {
            return reference(lhs.span, format!("unknown {kind} `{}` in {context}", lhs.name));
        }
        if !cod.contains(rhs.name.as_str()) {
            return reference(rhs.span, format!("unknown target {kind} `{}` in {context}", rhs.name));
        }
        if !seen.insert(lhs.name.as_str()) {
            return duplicate(lhs.span, format!("duplicate {kind} `{}` in {context}", lhs.name));
        }
        out.push((lhs.name.clone(), rhs.name.clone()));
    }
    if seen.len() != dom.len() {
        return p4_type_err(span, format!("{context} must assign every {kind}"));
    }
    Ok(out)
}

fn check_opt_arrow_map<E: InputError>(
    raw: &[(Ident, Option<Ident>, Span)],
    dom: &HashSet<&str>,
    cod: &HashSet<&str>,
    span: Span,
    kind: &str,
    context: &str,
) -> CResult<Vec<(String, Option<String>)>, E> {
    let mut seen = HashSet::new();
    let mut out = Vec::with_capacity(raw.len());
    for (lhs, rhs_opt, _) in raw {
        if !dom.contains(lhs.name.as_str()) {
            return reference(lhs.span, format!("unknown {kind} `{}` in {context}", lhs.name));
        }
        let rhs_str = if let Some(rhs) = rhs_opt {
            if !cod.contains(rhs.name.as_str()) {
                return reference(
                    rhs.span,
                    format!("unknown target {kind} `{}` in {context}", rhs.name),
                );
            }
            Some(rhs.name.clone())
        } else {
            None
        };
        if !seen.insert(lhs.name.as_str()) {
            return duplicate(lhs.span, format!("duplicate {kind} `{}` in {context}", lhs.name));
        }
        out.push((lhs.name.clone(), rhs_str));
    }
    if seen.len() != dom.len() {
        return p4_type_err(span, format!("{context} must assign every {kind}"));
    }
    Ok(out)
}

type ReadingSurjection = (Vec<(String, String)>, HashSet<String>);

fn check_reading_surjection<E: InputError>(
    raw: &[(Ident, Ident, Span)],
    sources: &HashSet<&str>,
    span: Span,
    context: &str,
) -> CResult<ReadingSurjection, E> {
    let mut seen = HashSet::new();
    let mut targets = HashSet::new();
    let mut out = Vec::with_capacity(raw.len());
    for (s, t, _) in raw {
        if !sources.contains(s.name.as_str()) {
            return reference(s.span, format!("unknown source `{}` in {context}", s.name));
        }
        if !seen.insert(s.name.as_str()) {
            return duplicate(s.span, format!("duplicate source `{}` in {context}", s.name));
        }
        targets.insert(t.name.clone());
        out.push((s.name.clone(), t.name.clone()));
    }
    if seen.len() != sources.len() {
        return p4_type_err(span, format!("{context} must assign every common source"));
    }
    Ok((out, targets))
}

pub(super) fn check_atlas<E: InputError>(
    raw: &RawAtlasTask,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    control: &Control,
) -> CResult<ShigureAtlasTask, E> {
    let name = full(reading_name, &[&raw.name.name]);
    let ctx = format!("`shigure atlas {name}`");
    let coeff_domain = check_coeff_domain(&raw.domain, control)?;
    let origins = check_p4_origins(&raw.origins, raw.span, &ctx)?;

    let (vertices, edges) = check_simple_graph(
        &raw.vertices,
        &raw.edges,
        &coeff_domain,
        r_idx,
        checker,
        raw.span,
        &ctx,
        control,
    )?;
    let v_set: HashSet<&str> = vertices.iter().map(String::as_str).collect();
    let e_set: HashSet<&str> = edges.iter().map(|e| e.name.as_str()).collect();

    let mu = check_p4_coord_value(&raw.mu.0, &coeff_domain, r_idx, checker, raw.mu.1, control)?;
    let base_lambdas = check_p4_coord_scalar_map(
        &raw.base_lambdas,
        &vertices,
        &coeff_domain,
        r_idx,
        checker,
        raw.span,
        "vertex",
        &format!("{ctx} base_lambdas"),
        control,
    )?;

    let allowed_vertices = check_p4_unique_idents(&raw.allowed_vertices, "allowed_vertex", &ctx)?;
    for v in &allowed_vertices {
        if !v_set.contains(v.as_str()) {
            return reference(raw.span, format!("unknown vertex `{v}` in allowed_vertices"));
        }
    }
    let allowed_edges = check_p4_unique_idents(&raw.allowed_edges, "allowed_edge", &ctx)?;
    for e in &allowed_edges {
        if !e_set.contains(e.as_str()) {
            return reference(raw.span, format!("unknown edge `{e}` in allowed_edges"));
        }
    }

    let refinement = raw
        .refinement
        .as_ref()
        .map(|r| {
            check_refinement(
                r.as_ref(),
                &v_set,
                &e_set,
                &coeff_domain,
                r_idx,
                checker,
                &ctx,
                control,
            )
            .map(Box::new)
        })
        .transpose()?;

    let extended_language_check = raw
        .extended_language_check
        .as_ref()
        .map(|ext| check_extended_language(ext, &coeff_domain, r_idx, checker, &ctx, control))
        .transpose()?;

    Ok(ShigureAtlasTask {
        name,
        reading: reading_name.to_owned(),
        coeff_domain,
        origins,
        vertices,
        edges,
        mu,
        base_lambdas,
        allowed_vertices,
        allowed_edges,
        compare_to_q: raw.compare_to_q,
        refinement,
        extended_language_check,
        span: raw.span,
    })
}

#[allow(clippy::too_many_arguments)]
fn check_refinement<E: InputError>(
    r: &RawAtlasRefinement,
    coarse_v: &HashSet<&str>,
    coarse_e: &HashSet<&str>,
    coeff_domain: &ShigureCoeffDomain,
    r_idx: usize,
    checker: &Checker<'_, E>,
    ctx: &str,
    control: &Control,
) -> CResult<ShigureAtlasRefinement, E> {
    let rctx = format!("{ctx} refinement");
    let (fine_vertices, fine_edges) = check_simple_graph(
        &r.fine_vertices,
        &r.fine_edges,
        coeff_domain,
        r_idx,
        checker,
        r.span,
        &format!("{rctx} fine_graph"),
        control,
    )?;
    let fine_v: HashSet<&str> = fine_vertices.iter().map(String::as_str).collect();
    let fine_e: HashSet<&str> = fine_edges.iter().map(|e| e.name.as_str()).collect();

    let vertex_map = check_total_arrow_map(
        &r.vertex_map,
        &fine_v,
        coarse_v,
        r.span,
        "vertex",
        &format!("{rctx} vertex_map"),
    )?;
    let edge_map = check_opt_arrow_map(
        &r.edge_map,
        &fine_e,
        coarse_e,
        r.span,
        "edge",
        &format!("{rctx} edge_map"),
    )?;

    if r.common_sources.is_empty() {
        return p4_type_err(r.span, format!("{rctx} common_sources must be non-empty"));
    }
    let common_sources = check_p4_unique_idents(&r.common_sources, "common_source", &rctx)?;
    let src_set: HashSet<&str> = common_sources.iter().map(String::as_str).collect();
    let (coarse_reading, coarse_t_owned) =
        check_reading_surjection(&r.coarse_reading, &src_set, r.span, &format!("{rctx} coarse_reading"))?;
    let (fine_reading, fine_t_owned) =
        check_reading_surjection(&r.fine_reading, &src_set, r.span, &format!("{rctx} fine_reading"))?;
    let coarse_t: HashSet<&str> = coarse_t_owned.iter().map(String::as_str).collect();
    let fine_t: HashSet<&str> = fine_t_owned.iter().map(String::as_str).collect();

    let coarse_nerve =
        check_supported_nerve(&r.coarse_nerve, &coarse_t, &format!("{rctx} coarse_nerve"), control)?;
    let fine_nerve =
        check_supported_nerve(&r.fine_nerve, &fine_t, &format!("{rctx} fine_nerve"), control)?;

    let c_charts: HashSet<&str> = coarse_nerve.charts.iter().map(|c| c.name.as_str()).collect();
    let f_charts: HashSet<&str> = fine_nerve.charts.iter().map(|c| c.name.as_str()).collect();
    let c_edges: HashSet<&str> = coarse_nerve.edges.iter().map(|e| e.name.as_str()).collect();
    let f_edges: HashSet<&str> = fine_nerve.edges.iter().map(|e| e.name.as_str()).collect();
    let c_faces: HashSet<&str> = coarse_nerve.faces.iter().map(|f| f.name.as_str()).collect();
    let f_faces: HashSet<&str> = fine_nerve.faces.iter().map(|f| f.name.as_str()).collect();

    let nerve_chart_map = check_total_arrow_map(
        &r.nerve_chart_map,
        &f_charts,
        &c_charts,
        r.span,
        "nerve_chart",
        &format!("{rctx} nerve_chart_map"),
    )?;
    let nerve_edge_map = check_opt_arrow_map(
        &r.nerve_edge_map,
        &f_edges,
        &c_edges,
        r.span,
        "nerve_edge",
        &format!("{rctx} nerve_edge_map"),
    )?;
    let nerve_face_map = check_opt_arrow_map(
        &r.nerve_face_map,
        &f_faces,
        &c_faces,
        r.span,
        "nerve_face",
        &format!("{rctx} nerve_face_map"),
    )?;

    let eval_condition = r
        .eval_condition
        .as_ref()
        .map(|ec| {
            if let Some(dup) = coarse_v.intersection(coarse_e).next() {
                return duplicate(
                    ec.span,
                    format!("coarse vertex/edge name collision `{dup}` in {rctx} eval_condition"),
                );
            }
            let mut scope: HashSet<&str> = coarse_v.clone();
            scope.extend(coarse_e.iter().copied());
            let evaluations = check_named_polys_in_scope(
                &ec.evaluations,
                coeff_domain,
                &scope,
                &format!("{rctx} eval_condition.evaluations"),
                control,
            )?;
            let equations = check_named_polys_in_scope(
                &ec.equations,
                coeff_domain,
                &scope,
                &format!("{rctx} eval_condition.equations"),
                control,
            )?;
            let invertibles = check_named_polys_in_scope(
                &ec.invertibles,
                coeff_domain,
                &scope,
                &format!("{rctx} eval_condition.invertibles"),
                control,
            )?;
            Ok::<_, E>(ShigureAtlasEvalCondition {
                evaluations,
                equations,
                invertibles,
                span: ec.span,
            })
        })
        .transpose()?;

    let forgetful_reading = r
        .forgetful_reading
        .as_ref()
        .map(|fg| {
            if fg.sample_values.is_empty() {
                return p4_type_err(fg.span, "forgetful_reading sample_values must be non-empty");
            }
            let fg_vars: HashSet<&str> = [fg.forgotten_var.name.as_str()].into_iter().collect();
            check_poly_literals(
                &fg.eval_expr,
                LiteralDomainRule::Exact(coeff_domain),
                fg.span,
                control,
            )?;
            check_poly_vars(
                &fg.eval_expr,
                &fg_vars,
                fg.span,
                "forgetful_reading.eval_expr",
                control,
            )?;
            check_poly_literals(
                &fg.condition_eq,
                LiteralDomainRule::Exact(coeff_domain),
                fg.span,
                control,
            )?;
            check_poly_vars(
                &fg.condition_eq,
                &fg_vars,
                fg.span,
                "forgetful_reading.condition_eq",
                control,
            )?;
            let mut samples = Vec::with_capacity(fg.sample_values.len());
            for sv in &fg.sample_values {
                samples.push(check_p4_coord_value(
                    sv,
                    coeff_domain,
                    r_idx,
                    checker,
                    fg.span,
                    control,
                )?);
            }
            Ok::<_, E>(ShigureForgetfulReading {
                forgotten_var: fg.forgotten_var.name.clone(),
                eval_expr: fg.eval_expr.clone(),
                condition_eq: fg.condition_eq.clone(),
                sample_values: samples,
                span: fg.span,
            })
        })
        .transpose()?;

    Ok(ShigureAtlasRefinement {
        fine_vertices,
        fine_edges,
        vertex_map,
        edge_map,
        common_sources,
        coarse_reading,
        fine_reading,
        coarse_nerve,
        fine_nerve,
        nerve_chart_map,
        nerve_edge_map,
        nerve_face_map,
        eval_condition,
        forgetful_reading,
        span: r.span,
    })
}

fn check_extended_language<E: InputError>(
    ext: &RawExtendedLanguageCheck,
    coeff_domain: &ShigureCoeffDomain,
    r_idx: usize,
    checker: &Checker<'_, E>,
    ctx: &str,
    control: &Control,
) -> CResult<ShigureExtendedLanguageCheck, E> {
    let ectx = format!("{ctx} extended_language_check");
    if ext.state_vars.is_empty() {
        return p4_type_err(ext.span, format!("{ectx} state_vars must be non-empty"));
    }
    let state_vars = check_p4_unique_idents(&ext.state_vars, "state_var", &ectx)?;
    let sv_set: HashSet<&str> = state_vars.iter().map(String::as_str).collect();
    let adapter_map = check_p4_poly_assign_map(
        &ext.adapter_map,
        &state_vars,
        &sv_set,
        coeff_domain,
        ext.span,
        "state_var",
        &format!("{ectx} adapter_map"),
        control,
    )?;

    let mut op_names = HashSet::new();
    let mut atomic_ops = Vec::with_capacity(ext.atomic_ops.len());
    for op in &ext.atomic_ops {
        if !op_names.insert(op.name.name.as_str()) {
            return duplicate(op.name.span, format!("duplicate atomic_op `{}`", op.name.name));
        }
        let arg_vars = check_p4_unique_idents(&op.arg_vars, "arg_var", &op.name.name)?;
        let mut scope = sv_set.clone();
        for a in &arg_vars {
            if sv_set.contains(a.as_str()) {
                return duplicate(
                    op.span,
                    format!("atomic_op `{}` arg `{a}` collides with state_var", op.name.name),
                );
            }
            scope.insert(a.as_str());
        }
        let before_updates = check_p4_poly_assign_map(
            &op.before_updates,
            &state_vars,
            &scope,
            coeff_domain,
            op.span,
            "state_var",
            &format!("atomic_op `{}` before", op.name.name),
            control,
        )?;
        let after_updates = check_p4_poly_assign_map(
            &op.after_updates,
            &state_vars,
            &scope,
            coeff_domain,
            op.span,
            "state_var",
            &format!("atomic_op `{}` after", op.name.name),
            control,
        )?;
        atomic_ops.push(ShigureAtomicOpCompare {
            name: op.name.name.clone(),
            arg_vars,
            before_updates,
            after_updates,
            span: op.span,
        });
    }

    let mut check_names = HashSet::new();
    let mut extended_checks = Vec::with_capacity(ext.extended_checks.len());
    for chk in &ext.extended_checks {
        match chk {
            RawExtendedOperationCheck::ProtocolSequence {
                name,
                extended_state_vars,
                initial_state,
                before_steps,
                after_steps,
                before_read,
                after_read,
                intermediate_laws,
                span,
            } => {
                if name.trim().is_empty() {
                    return p4_type_err(*span, "protocol_sequence name must be non-empty");
                }
                if !check_names.insert(name.as_str()) {
                    return duplicate(*span, format!("duplicate extended check `{name}`"));
                }
                if extended_state_vars.is_empty() {
                    return p4_type_err(
                        *span,
                        format!("protocol_sequence `{name}` extended_state_vars must be non-empty"),
                    );
                }
                let ext_vars =
                    check_p4_unique_idents(extended_state_vars, "extended_state_var", name)?;
                let ext_set: HashSet<&str> = ext_vars.iter().map(String::as_str).collect();
                let init = check_p4_coord_scalar_map(
                    initial_state,
                    &ext_vars,
                    coeff_domain,
                    r_idx,
                    checker,
                    *span,
                    "extended_state_var",
                    &format!("protocol_sequence `{name}` initial_state"),
                    control,
                )?;
                let mut b_steps = Vec::with_capacity(before_steps.len());
                for (i, st) in before_steps.iter().enumerate() {
                    b_steps.push(check_p4_poly_assign_map(
                        st,
                        &ext_vars,
                        &ext_set,
                        coeff_domain,
                        *span,
                        "extended_state_var",
                        &format!("protocol_sequence `{name}` before_step[{i}]"),
                        control,
                    )?);
                }
                let mut a_steps = Vec::with_capacity(after_steps.len());
                for (i, st) in after_steps.iter().enumerate() {
                    a_steps.push(check_p4_poly_assign_map(
                        st,
                        &ext_vars,
                        &ext_set,
                        coeff_domain,
                        *span,
                        "extended_state_var",
                        &format!("protocol_sequence `{name}` after_step[{i}]"),
                        control,
                    )?);
                }
                check_poly_literals(
                    before_read,
                    LiteralDomainRule::Exact(coeff_domain),
                    *span,
                    control,
                )?;
                check_poly_vars(
                    before_read,
                    &ext_set,
                    *span,
                    &format!("protocol_sequence `{name}` before_read"),
                    control,
                )?;
                check_poly_literals(
                    after_read,
                    LiteralDomainRule::Exact(coeff_domain),
                    *span,
                    control,
                )?;
                check_poly_vars(
                    after_read,
                    &ext_set,
                    *span,
                    &format!("protocol_sequence `{name}` after_read"),
                    control,
                )?;
                let ilaws = check_named_polys_in_scope(
                    intermediate_laws,
                    coeff_domain,
                    &ext_set,
                    &format!("protocol_sequence `{name}` intermediate_laws"),
                    control,
                )?;
                extended_checks.push(ShigureExtendedOperationCheck::ProtocolSequence {
                    name: name.clone(),
                    extended_state_vars: ext_vars,
                    initial_state: init,
                    before_steps: b_steps,
                    after_steps: a_steps,
                    before_read: before_read.clone(),
                    after_read: after_read.clone(),
                    intermediate_laws: ilaws,
                    span: *span,
                });
            }
            RawExtendedOperationCheck::RuntimeArgOp {
                name,
                before_updates,
                after_updates,
                sample_state,
                span,
            } => {
                if name.trim().is_empty() {
                    return p4_type_err(*span, "runtime_arg_op name must be non-empty");
                }
                if !check_names.insert(name.as_str()) {
                    return duplicate(*span, format!("duplicate extended check `{name}`"));
                }
                let bu = check_p4_poly_assign_map(
                    before_updates,
                    &state_vars,
                    &sv_set,
                    coeff_domain,
                    *span,
                    "state_var",
                    &format!("runtime_arg_op `{name}` before"),
                    control,
                )?;
                let au = check_p4_poly_assign_map(
                    after_updates,
                    &state_vars,
                    &sv_set,
                    coeff_domain,
                    *span,
                    "state_var",
                    &format!("runtime_arg_op `{name}` after"),
                    control,
                )?;
                let ss = check_p4_coord_scalar_map(
                    sample_state,
                    &state_vars,
                    coeff_domain,
                    r_idx,
                    checker,
                    *span,
                    "state_var",
                    &format!("runtime_arg_op `{name}` sample_state"),
                    control,
                )?;
                extended_checks.push(ShigureExtendedOperationCheck::RuntimeArgOp {
                    name: name.clone(),
                    before_updates: bu,
                    after_updates: au,
                    sample_state: ss,
                    span: *span,
                });
            }
        }
    }

    Ok(ShigureExtendedLanguageCheck {
        state_vars,
        adapter_map,
        atomic_ops,
        extended_checks,
        span: ext.span,
    })
}
