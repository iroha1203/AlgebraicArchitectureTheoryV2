//! `shigure path` 宣言の静的検査。

use super::ast_ext::*;
use super::check::{
    CResult, DeclCategory, LiteralDomainRule, check_poly_literals, check_poly_vars,
    check_presentation_vars, resolve_shigure_ref,
};
use super::check_ext_common::{
    ScopedMorphismMeta, check_eval_cond_against_domain_params, check_morphism_body,
    check_morphism_vars_against_pres, check_scalar_lit, check_scoped_change_spec_targets,
    check_state_law_list,
};
use super::*;
use crate::law::ast::Span;
use crate::law::check::{Checker, duplicate, full, reference};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;
use std::collections::{BTreeMap, HashMap, HashSet};

#[allow(clippy::too_many_arguments)]
pub(super) fn check_path<E: InputError>(
    raw: &RawPathTask,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span, usize)>,
    decls: &CheckedShigureDecls,
    reading_edges: &mut Vec<(usize, usize, Span)>,
    control: &Control,
) -> CResult<ShigurePathTask, E> {
    let full_name = full(reading_name, &[&raw.name.name]);
    let change_spec_name = resolve_shigure_ref(
        &raw.change_spec,
        DeclCategory::ChangeSpec,
        r_idx,
        reading_name,
        checker,
        index,
        reading_edges,
    )?;
    let spec = &decls.change_specs[&change_spec_name];
    let param_set: HashSet<&str> = spec.parameters.iter().map(|p| p.name.as_str()).collect();

    let eval_condition = match &raw.eval_condition {
        Some(q) => {
            let ec_name = resolve_shigure_ref(
                q,
                DeclCategory::EvalCondition,
                r_idx,
                reading_name,
                checker,
                index,
                reading_edges,
            )?;
            let ec = &decls.eval_conditions[&ec_name];
            check_eval_cond_against_domain_params(
                ec,
                &spec.coeff_domain,
                &param_set,
                raw.span,
                control,
            )?;
            Some(ec_name)
        }
        None => None,
    };

    match raw.kind {
        ShigurePathKind::FixedProtocolChangePath => check_fixed_path(
            raw,
            full_name,
            reading_name,
            r_idx,
            checker,
            index,
            decls,
            reading_edges,
            spec,
            &param_set,
            change_spec_name,
            eval_condition,
            control,
        ),
        ShigurePathKind::EnlargedProtocolExecutionPath => check_protocol_path(
            raw,
            full_name,
            reading_name,
            r_idx,
            checker,
            index,
            decls,
            reading_edges,
            spec,
            &param_set,
            change_spec_name,
            eval_condition,
            control,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn check_fixed_path<E: InputError>(
    raw: &RawPathTask,
    full_name: String,
    reading_name: &str,
    r_idx: usize,
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span, usize)>,
    decls: &CheckedShigureDecls,
    reading_edges: &mut Vec<(usize, usize, Span)>,
    spec: &ShigureChangeSpec,
    param_set: &HashSet<&str>,
    change_spec_name: String,
    eval_condition: Option<String>,
    control: &Control,
) -> CResult<ShigurePathTask, E> {
    if raw.protocol.is_some() {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw.span,
            "`fixed_protocol_change_path` must not specify `protocol`",
        ))
        .into());
    }
    let Some(raw_start) = &raw.start else {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw.span,
            "`fixed_protocol_change_path` requires a `start` endpoint",
        ))
        .into());
    };
    let Some(raw_end) = &raw.end else {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw.span,
            "`fixed_protocol_change_path` requires an `end` endpoint",
        ))
        .into());
    };

    let mut vertices_by_name: HashMap<String, &ShigurePresentation> = HashMap::new();
    let mut vertices_by_pres: BTreeMap<&str, Vec<(&ShigurePresentation, bool)>> = BTreeMap::new();
    let mut vertices = BTreeMap::new();
    for b in &raw.vertices {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if vertices_by_name.contains_key(&b.vertex.name) {
            return duplicate(
                b.vertex.span,
                format!("duplicate path vertex `{}`", b.vertex.name),
            );
        }
        let pres_name = resolve_shigure_ref(
            &b.presentation,
            DeclCategory::Presentation,
            r_idx,
            reading_name,
            checker,
            index,
            reading_edges,
        )?;
        let pres = &decls.presentations[&pres_name];
        if pres.coeff_domain != spec.coeff_domain {
            return Err(Box::new(Issue::law(
                Code::Type,
                b.span,
                format!(
                    "path vertex `{}` presentation coefficient domain does not match `change_spec`",
                    b.vertex.name
                ),
            ))
            .into());
        }
        check_presentation_vars(pres, Some(param_set), control)?;
        vertices_by_name.insert(b.vertex.name.clone(), pres);
        vertices_by_pres
            .entry(pres.name.as_str())
            .or_default()
            .push((pres, false));
        vertices.insert(b.vertex.name.clone(), pres_name);
    }

    let check_ep = |ep: &RawModelEndpoint, label: &str| -> CResult<ShigureModelEndpoint, E> {
        if !vertices_by_name.contains_key(&ep.vertex.name) {
            return reference(
                ep.vertex.span,
                format!(
                    "unknown path vertex `{}` in `{label}` endpoint",
                    ep.vertex.name
                ),
            );
        }
        let mut param_values = BTreeMap::new();
        for (p_name, lit, p_span) in &ep.param_values {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            if !param_set.contains(p_name.name.as_str()) {
                return reference(
                    p_name.span,
                    format!(
                        "unknown parameter `{}` in path `{label}` endpoint",
                        p_name.name
                    ),
                );
            }
            if param_values.contains_key(&p_name.name) {
                return duplicate(
                    p_name.span,
                    format!(
                        "duplicate parameter `{}` in path `{label}` endpoint",
                        p_name.name
                    ),
                );
            }
            check_scalar_lit(lit, &spec.coeff_domain, *p_span, control)?;
            param_values.insert(p_name.name.clone(), lit.clone());
        }
        Ok(ShigureModelEndpoint {
            vertex: ep.vertex.name.clone(),
            param_values,
            span: ep.span,
        })
    };
    let start = check_ep(raw_start, "start")?;
    let end = check_ep(raw_end, "end")?;

    let mut rules_by_name: HashMap<String, (String, String)> = HashMap::new();
    let mut rule_bodies: Vec<(ShigureMorphismBody, &ShigurePresentation)> =
        Vec::with_capacity(raw.rules.len() + 1);
    let mut rules = Vec::with_capacity(raw.rules.len());

    for r in &raw.rules {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if rules_by_name.contains_key(&r.name.name) {
            return duplicate(
                r.name.span,
                format!("duplicate one-step rule `{}`", r.name.name),
            );
        }
        let Some(&from_p) = vertices_by_name.get(&r.from_vertex.name) else {
            return reference(
                r.from_vertex.span,
                format!(
                    "unknown path vertex `{}` in rule `{}` from",
                    r.from_vertex.name, r.name.name
                ),
            );
        };
        let Some(&to_p) = vertices_by_name.get(&r.to_vertex.name) else {
            return reference(
                r.to_vertex.span,
                format!(
                    "unknown path vertex `{}` in rule `{}` to",
                    r.to_vertex.name, r.name.name
                ),
            );
        };

        let mut guard_names = HashSet::new();
        let mut param_guards = Vec::with_capacity(r.param_guards.len());
        for (g_name, g_expr, g_span) in &r.param_guards {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            if !guard_names.insert(g_name.name.clone()) {
                return duplicate(
                    g_name.span,
                    format!(
                        "duplicate guard `{}` in rule `{}`",
                        g_name.name, r.name.name
                    ),
                );
            }
            check_poly_literals(
                g_expr,
                LiteralDomainRule::Exact(&spec.coeff_domain),
                *g_span,
                control,
            )?;
            let ctx = format!("rule `{}` guard `{}`", r.name.name, g_name.name);
            check_poly_vars(g_expr, param_set, *g_span, &ctx, control)?;
            param_guards.push((g_name.name.clone(), g_expr.clone(), *g_span));
        }

        let mut param_updates = BTreeMap::new();
        for (p_name, u_expr, u_span) in &r.param_updates {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            if !param_set.contains(p_name.name.as_str()) {
                return reference(
                    p_name.span,
                    format!(
                        "unknown parameter `{}` in rule `{}` update",
                        p_name.name, r.name.name
                    ),
                );
            }
            if param_updates.contains_key(&p_name.name) {
                return duplicate(
                    p_name.span,
                    format!(
                        "duplicate update for parameter `{}` in rule `{}`",
                        p_name.name, r.name.name
                    ),
                );
            }
            check_poly_literals(
                u_expr,
                LiteralDomainRule::Exact(&spec.coeff_domain),
                *u_span,
                control,
            )?;
            let ctx = format!("rule `{}` update `{}`", r.name.name, p_name.name);
            check_poly_vars(u_expr, param_set, *u_span, &ctx, control)?;
            param_updates.insert(p_name.name.clone(), u_expr.clone());
        }

        let rule_ec = match &r.eval_condition {
            Some(q) => {
                let ec_name = resolve_shigure_ref(
                    q,
                    DeclCategory::EvalCondition,
                    r_idx,
                    reading_name,
                    checker,
                    index,
                    reading_edges,
                )?;
                let ec = &decls.eval_conditions[&ec_name];
                check_eval_cond_against_domain_params(
                    ec,
                    &spec.coeff_domain,
                    param_set,
                    r.span,
                    control,
                )?;
                Some(ec_name)
            }
            None => None,
        };

        let (m_src, m_tgt) = match raw.direction {
            ShigureDirection::StateMap => (from_p, to_p),
            ShigureDirection::TimeOrder => (to_p, from_p),
        };
        let morph = check_morphism_body(
            &r.morphism,
            r_idx,
            reading_name,
            checker,
            index,
            decls,
            reading_edges,
            m_src,
            m_tgt,
            Some(param_set),
            r.span,
            &format!("path rule `{}`", r.name.name),
            control,
        )?;
        rule_bodies.push((morph.clone(), m_src));
        rules_by_name.insert(
            r.name.name.clone(),
            (r.from_vertex.name.clone(), r.to_vertex.name.clone()),
        );
        rules.push(ShigureOneStepRule {
            name: r.name.name.clone(),
            from_vertex: r.from_vertex.name.clone(),
            to_vertex: r.to_vertex.name.clone(),
            param_guards,
            param_updates,
            morphism: morph,
            eval_condition: rule_ec,
            span: r.span,
        });
    }

    let query_mode = match &raw.query_mode {
        RawPathQueryMode::Find => ShigurePathQueryMode::Find,
        RawPathQueryMode::Concatenate { first, second } => {
            let check_seq = |seq: &[Ident],
                             start_v: &str,
                             label: &str|
             -> CResult<(String, Vec<String>), E> {
                let mut cur = start_v.to_owned();
                let mut names = Vec::with_capacity(seq.len());
                for id in seq {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    let Some((from_v, to_v)) = rules_by_name.get(&id.name) else {
                        return reference(
                            id.span,
                            format!("unknown rule `{}` in `mode concatenate` {label}", id.name),
                        );
                    };
                    if *from_v != cur {
                        return Err(Box::new(Issue::law(
                                Code::Type,
                                id.span,
                                format!(
                                    "path concatenate `{label}` rule `{}` expects vertex `{cur}`, got `{from_v}`",
                                    id.name
                                ),
                            ))
                            .into());
                    }
                    cur = to_v.clone();
                    names.push(id.name.clone());
                }
                Ok((cur, names))
            };
            let (mid, first_names) = check_seq(first, &start.vertex, "first")?;
            let (final_v, second_names) = check_seq(second, &mid, "second")?;
            if final_v != end.vertex {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    raw.span,
                    format!(
                        "path concatenate ends at vertex `{final_v}`, expected `{}`",
                        end.vertex
                    ),
                ))
                .into());
            }
            ShigurePathQueryMode::Concatenate {
                first: first_names,
                second: second_names,
            }
        }
        RawPathQueryMode::Subdivide { target_edge } => {
            let start_p = vertices_by_name[&start.vertex];
            let end_p = vertices_by_name[&end.vertex];
            let (m_src, m_tgt) = match raw.direction {
                ShigureDirection::StateMap => (start_p, end_p),
                ShigureDirection::TimeOrder => (end_p, start_p),
            };
            let target_morph = check_morphism_body(
                target_edge,
                r_idx,
                reading_name,
                checker,
                index,
                decls,
                reading_edges,
                m_src,
                m_tgt,
                Some(param_set),
                raw.span,
                "`mode subdivide` target_edge",
                control,
            )?;
            rule_bodies.push((target_morph.clone(), m_src));
            ShigurePathQueryMode::Subdivide {
                target_edge: target_morph,
            }
        }
    };

    let morphs: Vec<ScopedMorphismMeta<'_>> = rule_bodies
        .iter()
        .map(|(body, src_p)| ScopedMorphismMeta::from_body(body, src_p, decls, false))
        .collect();
    check_scoped_change_spec_targets(spec, &vertices_by_pres, &morphs, "path", control)?;

    Ok(ShigurePathTask {
        name: full_name,
        reading: reading_name.to_owned(),
        kind: raw.kind,
        direction: raw.direction,
        query_mode,
        length: raw.length,
        vertices,
        rules,
        start: Some(start),
        end: Some(end),
        protocol: None,
        change_spec: change_spec_name,
        eval_condition,
        span: raw.span,
    })
}

#[allow(clippy::too_many_arguments)]
fn check_protocol_path<E: InputError>(
    raw: &RawPathTask,
    full_name: String,
    reading_name: &str,
    r_idx: usize,
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span, usize)>,
    decls: &CheckedShigureDecls,
    reading_edges: &mut Vec<(usize, usize, Span)>,
    spec: &ShigureChangeSpec,
    param_set: &HashSet<&str>,
    change_spec_name: String,
    eval_condition: Option<String>,
    control: &Control,
) -> CResult<ShigurePathTask, E> {
    if !matches!(raw.query_mode, RawPathQueryMode::Find) {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw.span,
            "`enlarged_protocol_execution_path` only supports `mode find`",
        ))
        .into());
    }
    if !raw.rules.is_empty() {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw.span,
            "`enlarged_protocol_execution_path` must not define `rule` entries",
        ))
        .into());
    }
    if !raw.vertices.is_empty() || raw.start.is_some() || raw.end.is_some() {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw.span,
            "`enlarged_protocol_execution_path` must not specify `vertex`, `start`, or `end`",
        ))
        .into());
    }
    let Some(raw_proto) = &raw.protocol else {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw.span,
            "`enlarged_protocol_execution_path` requires a `protocol` block",
        ))
        .into());
    };

    let cmp_name = resolve_shigure_ref(
        &raw_proto.comparison,
        DeclCategory::Comparison,
        r_idx,
        reading_name,
        checker,
        index,
        reading_edges,
    )?;
    let cmp = &decls.comparisons[&cmp_name];
    let before_p = &decls.presentations[&cmp.before];
    let after_p = &decls.presentations[&cmp.after];
    if spec.coeff_domain != before_p.coeff_domain {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw_proto.span,
            "`change_spec` coefficient domain must match `protocol` presentations",
        ))
        .into());
    }
    check_presentation_vars(after_p, Some(param_set), control)?;
    check_morphism_vars_against_pres(
        &cmp.state_comparisons,
        &cmp.word_translation,
        after_p,
        Some(param_set),
        &cmp.name,
        raw_proto.span,
        control,
    )?;

    let cmp_body = ShigureMorphismBody::Comparison(cmp_name.clone());
    let mut pres_map = BTreeMap::new();
    pres_map.insert(before_p.name.as_str(), vec![(before_p, true)]);
    pres_map.insert(after_p.name.as_str(), vec![(after_p, false)]);
    let morphs = vec![ScopedMorphismMeta::from_body(
        &cmp_body, after_p, decls, false,
    )];
    check_scoped_change_spec_targets(spec, &pres_map, &morphs, "protocol path", control)?;

    let Some(start_ph) = after_p
        .phases
        .iter()
        .find(|p| p.name == raw_proto.start_phase.name)
    else {
        return reference(
            raw_proto.start_phase.span,
            format!(
                "unknown after phase `{}` in protocol `start_phase`",
                raw_proto.start_phase.name
            ),
        );
    };
    let Some(end_ph) = after_p
        .phases
        .iter()
        .find(|p| p.name == raw_proto.end_phase.name)
    else {
        return reference(
            raw_proto.end_phase.span,
            format!(
                "unknown after phase `{}` in protocol `end_phase`",
                raw_proto.end_phase.name
            ),
        );
    };

    let start_laws = check_state_law_list(
        &raw_proto.start_laws,
        &spec.coeff_domain,
        "protocol start_law",
        control,
    )?;
    let mut start_allowed: HashSet<&str> =
        start_ph.coords.iter().map(|c| c.name.as_str()).collect();
    start_allowed.extend(param_set.iter().copied());
    for l in &start_laws {
        let ctx = format!("{full_name}.protocol.start_law.{}", l.name);
        check_poly_vars(&l.expr, &start_allowed, l.span, &ctx, control)?;
    }

    let end_laws = check_state_law_list(
        &raw_proto.end_laws,
        &spec.coeff_domain,
        "protocol end_law",
        control,
    )?;
    let mut end_allowed: HashSet<&str> = end_ph.coords.iter().map(|c| c.name.as_str()).collect();
    end_allowed.extend(param_set.iter().copied());
    for l in &end_laws {
        let ctx = format!("{full_name}.protocol.end_law.{}", l.name);
        check_poly_vars(&l.expr, &end_allowed, l.span, &ctx, control)?;
    }

    if raw_proto.allowed_ops.is_empty() {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw_proto.span,
            "`protocol` `allowed_ops` must not be empty",
        ))
        .into());
    }
    let mut seen_ops = HashSet::new();
    let mut allowed_ops = Vec::with_capacity(raw_proto.allowed_ops.len());
    for op_id in &raw_proto.allowed_ops {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !seen_ops.insert(op_id.name.clone()) {
            return duplicate(
                op_id.span,
                format!("duplicate operation `{}` in `allowed_ops`", op_id.name),
            );
        }
        if !after_p.operations.iter().any(|o| o.name == op_id.name) {
            return reference(
                op_id.span,
                format!(
                    "unknown operation `{}` on `{}` in `allowed_ops`",
                    op_id.name, after_p.name
                ),
            );
        }
        allowed_ops.push(op_id.name.clone());
    }

    Ok(ShigurePathTask {
        name: full_name,
        reading: reading_name.to_owned(),
        kind: raw.kind,
        direction: raw.direction,
        query_mode: ShigurePathQueryMode::Find,
        length: raw.length,
        vertices: BTreeMap::new(),
        rules: Vec::new(),
        start: None,
        end: None,
        protocol: Some(ShigureProtocolExecution {
            comparison: cmp_name,
            start_phase: raw_proto.start_phase.name.clone(),
            start_laws,
            end_phase: raw_proto.end_phase.name.clone(),
            end_laws,
            allowed_ops,
            span: raw_proto.span,
        }),
        change_spec: change_spec_name,
        eval_condition,
        span: raw.span,
    })
}
