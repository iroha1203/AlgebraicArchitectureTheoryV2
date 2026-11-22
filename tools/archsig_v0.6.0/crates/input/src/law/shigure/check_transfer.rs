//! `shigure transfer` 宣言の静的検査。

use super::ast_ext::*;
use super::check::{
    CResult, DeclCategory, LiteralDomainRule, check_poly_literals, check_poly_vars,
    check_presentation_vars, resolve_shigure_ref,
};
use super::check_ext_common::{
    ScopedMorphismMeta, check_eval_cond_against_domain_params, check_morphism_body,
    check_morphism_vars_against_pres, check_scoped_change_spec_targets, check_state_law_list,
};
use super::*;
use crate::law::ast::Span;
use crate::law::check::{Checker, duplicate, full, reference};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;
use std::collections::{BTreeMap, HashMap, HashSet};

#[allow(clippy::too_many_arguments)]
pub(super) fn check_transfer<E: InputError>(
    raw: &RawTransferTask,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span, usize)>,
    decls: &CheckedShigureDecls,
    reading_edges: &mut Vec<(usize, usize, Span)>,
    control: &Control,
) -> CResult<ShigureTransferTask, E> {
    let full_name = full(reading_name, &[&raw.name.name]);
    if raw.steps.is_empty() {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw.span,
            "`shigure transfer` requires at least one `step`",
        ))
        .into());
    }

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

    let mut step_names = HashSet::new();
    let mut pres_map: BTreeMap<&str, Vec<(&ShigurePresentation, bool)>> = BTreeMap::new();
    let mut step_metas: Vec<(ShigureMorphismBody, &ShigurePresentation)> =
        Vec::with_capacity(raw.steps.len());
    let mut steps = Vec::with_capacity(raw.steps.len());
    let mut first_before: Option<(&ShigurePresentation, &str)> = None;
    let mut prev_after: Option<(&ShigurePresentation, &str)> = None;

    for (idx, st) in raw.steps.iter().enumerate() {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !step_names.insert(st.name.name.clone()) {
            return duplicate(
                st.name.span,
                format!("duplicate transfer step `{}`", st.name.name),
            );
        }

        let (source, before_p, after_p, morph_body) = match &st.source {
            RawTransferStepSource::Comparison(q) => {
                let cmp_name = resolve_shigure_ref(
                    q,
                    DeclCategory::Comparison,
                    r_idx,
                    reading_name,
                    checker,
                    index,
                    reading_edges,
                )?;
                let cmp = &decls.comparisons[&cmp_name];
                let b_p = &decls.presentations[&cmp.before];
                let a_p = &decls.presentations[&cmp.after];
                if b_p.coeff_domain != spec.coeff_domain {
                    return Err(Box::new(Issue::law(
                        Code::Type,
                        st.span,
                        format!(
                            "transfer step `{}` comparison domain does not match `change_spec`",
                            st.name.name
                        ),
                    ))
                    .into());
                }
                check_presentation_vars(a_p, Some(&param_set), control)?;
                check_morphism_vars_against_pres(
                    &cmp.state_comparisons,
                    &cmp.word_translation,
                    a_p,
                    Some(&param_set),
                    &format!("transfer step `{}`", st.name.name),
                    st.span,
                    control,
                )?;
                let body = ShigureMorphismBody::Comparison(cmp_name.clone());
                (
                    ShigureTransferStepSource::Comparison(cmp_name),
                    b_p,
                    a_p,
                    body,
                )
            }
            RawTransferStepSource::Inline {
                before,
                after,
                morphism,
            } => {
                let b_name = resolve_shigure_ref(
                    before,
                    DeclCategory::Presentation,
                    r_idx,
                    reading_name,
                    checker,
                    index,
                    reading_edges,
                )?;
                let a_name = resolve_shigure_ref(
                    after,
                    DeclCategory::Presentation,
                    r_idx,
                    reading_name,
                    checker,
                    index,
                    reading_edges,
                )?;
                let b_p = &decls.presentations[&b_name];
                let a_p = &decls.presentations[&a_name];
                if b_p.coeff_domain != spec.coeff_domain || a_p.coeff_domain != spec.coeff_domain {
                    return Err(Box::new(Issue::law(
                        Code::Type,
                        st.span,
                        format!(
                            "transfer step `{}` presentation domain does not match `change_spec`",
                            st.name.name
                        ),
                    ))
                    .into());
                }
                check_presentation_vars(b_p, Some(&param_set), control)?;
                check_presentation_vars(a_p, Some(&param_set), control)?;
                let body = check_morphism_body(
                    morphism,
                    r_idx,
                    reading_name,
                    checker,
                    index,
                    decls,
                    reading_edges,
                    a_p,
                    b_p,
                    Some(&param_set),
                    st.span,
                    &format!("transfer step `{}`", st.name.name),
                    control,
                )?;
                (
                    ShigureTransferStepSource::Inline {
                        before: b_name,
                        after: a_name,
                        morphism: body.clone(),
                    },
                    b_p,
                    a_p,
                    body,
                )
            }
        };

        let Some(src_ph) = before_p
            .phases
            .iter()
            .find(|p| p.name == st.source_phase.name)
        else {
            return reference(
                st.source_phase.span,
                format!(
                    "unknown source_phase `{}` on `{}` in step `{}`",
                    st.source_phase.name, before_p.name, st.name.name
                ),
            );
        };
        let Some(tgt_ph) = after_p
            .phases
            .iter()
            .find(|p| p.name == st.target_phase.name)
        else {
            return reference(
                st.target_phase.span,
                format!(
                    "unknown target_phase `{}` on `{}` in step `{}`",
                    st.target_phase.name, after_p.name, st.name.name
                ),
            );
        };

        let mapped_before_phase = match &morph_body {
            ShigureMorphismBody::Comparison(c) => decls.comparisons[c]
                .state_comparisons
                .iter()
                .find(|s| s.after_phase == tgt_ph.name)
                .map(|s| s.before_phase.as_str()),
            ShigureMorphismBody::Inline {
                state_comparisons, ..
            } => state_comparisons
                .iter()
                .find(|s| s.after_phase == tgt_ph.name)
                .map(|s| s.before_phase.as_str()),
            ShigureMorphismBody::Identity => Some(tgt_ph.name.as_str()),
        };
        if mapped_before_phase != Some(src_ph.name.as_str()) {
            return Err(Box::new(Issue::law(
                Code::Type,
                st.span,
                format!(
                    "transfer step `{}`: morphism maps target_phase `{}` to `{:?}`, expected source_phase `{}`",
                    st.name.name, tgt_ph.name, mapped_before_phase, src_ph.name
                ),
            ))
            .into());
        }

        if idx == 0 {
            first_before = Some((before_p, src_ph.name.as_str()));
        } else if let Some((prev_a, prev_tgt_ph)) = prev_after {
            if before_p.name != prev_a.name {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    st.span,
                    format!(
                        "transfer chain discontinuity at step `{}`: before `{}` != previous after `{}`",
                        st.name.name, before_p.name, prev_a.name
                    ),
                ))
                .into());
            }
            if src_ph.name != prev_tgt_ph {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    st.span,
                    format!(
                        "transfer chain phase discontinuity at step `{}`: source_phase `{}` != previous target_phase `{prev_tgt_ph}`",
                        st.name.name, src_ph.name
                    ),
                ))
                .into());
            }
        }
        prev_after = Some((after_p, tgt_ph.name.as_str()));

        let mut src_allowed: HashSet<&str> =
            src_ph.coords.iter().map(|c| c.name.as_str()).collect();
        src_allowed.extend(param_set.iter().copied());

        let domain_laws = check_state_law_list(
            &st.domain_laws,
            &spec.coeff_domain,
            &format!("transfer step `{}` domain_law", st.name.name),
            control,
        )?;
        for l in &domain_laws {
            let ctx = format!("{}.{}.domain_law.{}", full_name, st.name.name, l.name);
            check_poly_vars(&l.expr, &src_allowed, l.span, &ctx, control)?;
        }

        let mut lift_map = BTreeMap::new();
        for (coord_id, expr, l_span) in &st.lift_map {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            if !tgt_ph.coords.iter().any(|c| c.name == coord_id.name) {
                return reference(
                    coord_id.span,
                    format!(
                        "unknown target coordinate `{}` in phase `{}` (step `{}` lift)",
                        coord_id.name, tgt_ph.name, st.name.name
                    ),
                );
            }
            if lift_map.contains_key(&coord_id.name) {
                return duplicate(
                    coord_id.span,
                    format!(
                        "duplicate lift assignment for `{}` in step `{}`",
                        coord_id.name, st.name.name
                    ),
                );
            }
            check_poly_literals(
                expr,
                LiteralDomainRule::Exact(&spec.coeff_domain),
                *l_span,
                control,
            )?;
            let ctx = format!("{}.{}.lift.{}", full_name, st.name.name, coord_id.name);
            check_poly_vars(expr, &src_allowed, *l_span, &ctx, control)?;
            lift_map.insert(coord_id.name.clone(), expr.clone());
        }
        if lift_map.len() != tgt_ph.coords.len() {
            return Err(Box::new(Issue::law(
                Code::Type,
                st.span,
                format!(
                    "transfer step `{}` `lift` must assign every coordinate of target phase `{}`",
                    st.name.name, tgt_ph.name
                ),
            ))
            .into());
        }

        pres_map
            .entry(before_p.name.as_str())
            .or_default()
            .push((before_p, false));
        pres_map
            .entry(after_p.name.as_str())
            .or_default()
            .push((after_p, false));
        step_metas.push((morph_body, after_p));
        steps.push(ShigureTransferStep {
            name: st.name.name.clone(),
            source,
            source_phase: st.source_phase.name.clone(),
            target_phase: st.target_phase.name.clone(),
            domain_laws,
            lift_map,
            span: st.span,
        });
    }

    let morphs: Vec<ScopedMorphismMeta<'_>> = step_metas
        .iter()
        .map(|(body, a_p)| ScopedMorphismMeta::from_body(body, a_p, decls, false))
        .collect();
    check_scoped_change_spec_targets(spec, &pres_map, &morphs, "transfer", control)?;

    let (first_before_p, first_src_ph) = first_before.expect("non-empty steps");
    let (last_after_p, last_tgt_ph) = prev_after.expect("non-empty steps");

    let mut wc_names = HashSet::new();
    let mut word_checks = Vec::with_capacity(raw.word_checks.len());
    for wc in &raw.word_checks {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !wc_names.insert(wc.name.name.clone()) {
            return duplicate(
                wc.name.span,
                format!("duplicate `word_check` `{}`", wc.name.name),
            );
        }
        let (args, w_steps) = check_word_steps(
            &wc.args,
            &wc.steps,
            last_after_p,
            last_tgt_ph,
            &spec.coeff_domain,
            &param_set,
            &format!("word_check `{}`", wc.name.name),
            control,
        )?;
        word_checks.push(ShigureWordCheck {
            name: wc.name.name.clone(),
            args,
            steps: w_steps,
            span: wc.span,
        });
    }

    let mut ol_names = HashSet::new();
    let mut old_word_lifts = Vec::with_capacity(raw.old_word_lifts.len());
    for ol in &raw.old_word_lifts {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !ol_names.insert(ol.name.name.clone()) {
            return duplicate(
                ol.name.span,
                format!("duplicate `old_word_lift` `{}`", ol.name.name),
            );
        }
        let (args, target_steps) = check_word_steps(
            &ol.args,
            &ol.target_steps,
            first_before_p,
            first_src_ph,
            &spec.coeff_domain,
            &param_set,
            &format!("old_word_lift `{}`", ol.name.name),
            control,
        )?;
        old_word_lifts.push(ShigureOldWordLift {
            name: ol.name.name.clone(),
            args,
            target_steps,
            max_length: ol.max_length,
            span: ol.span,
        });
    }

    Ok(ShigureTransferTask {
        name: full_name,
        reading: reading_name.to_owned(),
        steps,
        word_checks,
        old_word_lifts,
        change_spec: change_spec_name,
        eval_condition,
        require_full_domain: raw.require_full_domain,
        span: raw.span,
    })
}

#[allow(clippy::too_many_arguments)]
fn check_word_steps<E: InputError>(
    raw_args: &[Ident],
    raw_steps: &[RawWordStep],
    pres: &ShigurePresentation,
    start_phase: &str,
    domain: &ShigureCoeffDomain,
    param_set: &HashSet<&str>,
    context: &str,
    control: &Control,
) -> CResult<(Vec<String>, Vec<ShigureWordStep>), E> {
    let mut seen_args = HashSet::new();
    let mut args = Vec::with_capacity(raw_args.len());
    for a in raw_args {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if param_set.contains(a.name.as_str()) {
            return duplicate(
                a.span,
                format!(
                    "argument `{}` in {context} collides with change_spec parameter",
                    a.name
                ),
            );
        }
        if !seen_args.insert(a.name.clone()) {
            return duplicate(
                a.span,
                format!("duplicate argument `{}` in {context}", a.name),
            );
        }
        args.push(a.name.clone());
    }
    let mut allowed: HashSet<&str> = seen_args.iter().map(String::as_str).collect();
    allowed.extend(param_set.iter().copied());

    let mut cur_phase = start_phase;
    let mut steps = Vec::with_capacity(raw_steps.len());
    for (idx, st) in raw_steps.iter().enumerate() {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        let Some(op) = pres.operations.iter().find(|o| o.name == st.operation.name) else {
            return reference(
                st.operation.span,
                format!(
                    "unknown operation `{}` on `{}` in {context} step {idx}",
                    st.operation.name, pres.name
                ),
            );
        };
        if op.source_phase != cur_phase {
            return Err(Box::new(Issue::law(
                Code::Type,
                st.operation.span,
                format!(
                    "{context} step {idx}: operation `{}` expects phase `{cur_phase}`, got `{}`",
                    op.name, op.source_phase
                ),
            ))
            .into());
        }
        if st.arg_exprs.len() != op.args.len() {
            return Err(Box::new(Issue::law(
                Code::Type,
                st.span,
                format!(
                    "{context} step {idx} (`{}`) expects {} arguments, got {}",
                    op.name,
                    op.args.len(),
                    st.arg_exprs.len()
                ),
            ))
            .into());
        }
        for expr in &st.arg_exprs {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            check_poly_literals(expr, LiteralDomainRule::Exact(domain), st.span, control)?;
            check_poly_vars(expr, &allowed, st.span, context, control)?;
        }
        cur_phase = op.target_phase.as_str();
        steps.push(ShigureWordStep {
            operation: st.operation.name.clone(),
            arg_exprs: st.arg_exprs.clone(),
            span: st.span,
        });
    }
    Ok((args, steps))
}
