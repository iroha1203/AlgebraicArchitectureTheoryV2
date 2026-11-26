//! `shigure diagram`・`shigure path`・`shigure transfer` の射本体・変数名前空間検査ヘルパ。

use super::ast_ext::*;
use super::check::{
    CResult, DeclCategory, LiteralDomainRule, ShigureDeclCtx, check_poly_literals, check_poly_vars,
};
use super::check_ext_common::check_coords_disjoint_from_params;
use super::*;
use crate::law::ast::Span;
use crate::law::check::{duplicate, reference};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;
use std::collections::{HashMap, HashSet};

pub(super) struct MorphismCheckSpec<'a> {
    pub(super) src_pres: &'a ShigurePresentation,
    pub(super) tgt_pres: &'a ShigurePresentation,
    pub(super) params: Option<&'a HashSet<&'a str>>,
    pub(super) span: Span,
    pub(super) context: &'a str,
}

pub(super) fn check_morphism_body<E: InputError>(
    raw: &RawMorphismBody,
    ctx: &mut ShigureDeclCtx<'_, '_, E>,
    spec: &MorphismCheckSpec<'_>,
) -> CResult<ShigureMorphismBody, E> {
    let MorphismCheckSpec {
        src_pres: morph_src_pres,
        tgt_pres: morph_tgt_pres,
        params,
        span,
        context,
    } = *spec;
    let control = ctx.control;
    if morph_src_pres.coeff_domain != morph_tgt_pres.coeff_domain {
        return Err(Box::new(Issue::law(
            Code::Type,
            span,
            format!("{context} endpoints must share the same coefficient domain"),
        ))
        .into());
    }
    match raw {
        RawMorphismBody::Comparison(qname) => {
            let cmp_name = ctx.resolve_ref(qname, DeclCategory::Comparison)?;
            let cmp = &ctx.decls.comparisons[&cmp_name];
            if cmp.after != morph_src_pres.name || cmp.before != morph_tgt_pres.name {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    span,
                    format!(
                        "{context}: comparison `{}` maps `{} -> {}`, expected `{} -> {}`",
                        cmp.name, cmp.after, cmp.before, morph_src_pres.name, morph_tgt_pres.name
                    ),
                ))
                .into());
            }
            check_morphism_vars_against_pres(
                &cmp.state_comparisons,
                &cmp.word_translation,
                morph_src_pres,
                params,
                context,
                span,
                control,
            )?;
            Ok(ShigureMorphismBody::Comparison(cmp_name))
        }
        RawMorphismBody::Identity(id_span) => {
            check_identity_compatibility(
                morph_src_pres,
                morph_tgt_pres,
                *id_span,
                context,
                control,
            )?;
            Ok(ShigureMorphismBody::Identity)
        }
        RawMorphismBody::Inline {
            state_comparisons,
            word_translation,
        } => {
            let (scs, wt) = check_inline_morphism_parts(
                state_comparisons,
                word_translation,
                morph_src_pres,
                morph_tgt_pres,
                span,
                context,
                control,
            )?;
            check_morphism_vars_against_pres(
                &scs,
                &wt,
                morph_src_pres,
                params,
                context,
                span,
                control,
            )?;
            Ok(ShigureMorphismBody::Inline {
                state_comparisons: scs,
                word_translation: wt,
            })
        }
    }
}

fn check_identity_compatibility<E: InputError>(
    src: &ShigurePresentation,
    tgt: &ShigurePresentation,
    span: Span,
    context: &str,
    control: &Control,
) -> CResult<(), E> {
    for s_ph in &src.phases {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        let Some(t_ph) = tgt.phases.iter().find(|p| p.name == s_ph.name) else {
            return Err(Box::new(Issue::law(
                Code::Type,
                span,
                format!(
                    "{context} `identity`: target `{}` is missing phase `{}`",
                    tgt.name, s_ph.name
                ),
            ))
            .into());
        };
        let s_coords: HashSet<&str> = s_ph.coords.iter().map(|c| c.name.as_str()).collect();
        let t_coords: HashSet<&str> = t_ph.coords.iter().map(|c| c.name.as_str()).collect();
        if s_coords != t_coords {
            return Err(Box::new(Issue::law(
                Code::Type,
                span,
                format!(
                    "{context} `identity`: coordinates in phase `{}` differ between `{}` and `{}`",
                    s_ph.name, src.name, tgt.name
                ),
            ))
            .into());
        }
        for t_obs in tgt.observations.iter().filter(|o| o.phase == t_ph.name) {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            let Some(s_obs) = src
                .observations
                .iter()
                .find(|o| o.phase == s_ph.name && o.name == t_obs.name)
            else {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    span,
                    format!(
                        "{context} `identity`: `{}` phase `{}` is missing observation `{}`",
                        src.name, s_ph.name, t_obs.name
                    ),
                ))
                .into());
            };
            if s_obs.components.len() != t_obs.components.len() {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    span,
                    format!(
                        "{context} `identity`: observation `{}` arity mismatch on phase `{}`",
                        t_obs.name, s_ph.name
                    ),
                ))
                .into());
            }
        }
    }
    for s_op in &src.operations {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        let Some(t_op) = tgt.operations.iter().find(|o| o.name == s_op.name) else {
            return Err(Box::new(Issue::law(
                Code::Type,
                span,
                format!(
                    "{context} `identity`: target `{}` is missing operation `{}`",
                    tgt.name, s_op.name
                ),
            ))
            .into());
        };
        if t_op.source_phase != s_op.source_phase
            || t_op.target_phase != s_op.target_phase
            || t_op.args.len() != s_op.args.len()
        {
            return Err(Box::new(Issue::law(
                Code::Type,
                span,
                format!(
                    "{context} `identity`: operation `{}` signature mismatch between `{}` and `{}`",
                    s_op.name, src.name, tgt.name
                ),
            ))
            .into());
        }
    }
    Ok(())
}

fn check_inline_morphism_parts<E: InputError>(
    raw_scs: &[RawStateComparison],
    raw_wt: &[RawTranslatedWord],
    src_pres: &ShigurePresentation,
    tgt_pres: &ShigurePresentation,
    span: Span,
    context: &str,
    control: &Control,
) -> CResult<(Vec<ShigureStateComparison>, Vec<ShigureTranslatedWord>), E> {
    let mut phase_map = HashMap::new();
    let mut scs = Vec::with_capacity(raw_scs.len());
    for sc in raw_scs {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !src_pres
            .phases
            .iter()
            .any(|p| p.name == sc.after_phase.name)
        {
            return reference(
                sc.after_phase.span,
                format!(
                    "unknown source phase `{}` in {context}",
                    sc.after_phase.name
                ),
            );
        }
        let Some(t_ph) = tgt_pres
            .phases
            .iter()
            .find(|p| p.name == sc.before_phase.name)
        else {
            return reference(
                sc.before_phase.span,
                format!(
                    "unknown target phase `{}` in {context}",
                    sc.before_phase.name
                ),
            );
        };
        if phase_map
            .insert(sc.after_phase.name.clone(), sc.before_phase.name.clone())
            .is_some()
        {
            return duplicate(
                sc.after_phase.span,
                format!(
                    "duplicate state_map for phase `{}` in {context}",
                    sc.after_phase.name
                ),
            );
        }
        let mut seen_coords = HashSet::new();
        let mut map = Vec::with_capacity(sc.map.len());
        for (coord, expr) in &sc.map {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            if !t_ph.coords.iter().any(|c| c.name == coord.name) {
                return reference(
                    coord.span,
                    format!(
                        "unknown target coordinate `{}` in phase `{}` ({context})",
                        coord.name, t_ph.name
                    ),
                );
            }
            if !seen_coords.insert(coord.name.clone()) {
                return duplicate(
                    coord.span,
                    format!("duplicate state_map entry for coordinate `{}`", coord.name),
                );
            }
            check_poly_literals(
                expr,
                LiteralDomainRule::Exact(&src_pres.coeff_domain),
                sc.span,
                control,
            )?;
            map.push((coord.name.clone(), expr.clone()));
        }
        if seen_coords.len() != t_ph.coords.len() {
            return Err(Box::new(Issue::law(
                Code::Type,
                sc.span,
                format!(
                    "state_map `{}` -> `{}` in {context} must assign every coordinate of `{}`",
                    sc.after_phase.name, t_ph.name, t_ph.name
                ),
            ))
            .into());
        }
        for t_obs in tgt_pres
            .observations
            .iter()
            .filter(|o| o.phase == t_ph.name)
        {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            let Some(s_obs) = src_pres
                .observations
                .iter()
                .find(|o| o.phase == sc.after_phase.name && o.name == t_obs.name)
            else {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    sc.span,
                    format!(
                        "phase `{}` of `{}` is missing observation `{}` required by `{}.{}`",
                        sc.after_phase.name, src_pres.name, t_obs.name, tgt_pres.name, t_ph.name
                    ),
                ))
                .into());
            };
            if s_obs.components.len() != t_obs.components.len() {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    sc.span,
                    format!(
                        "observation `{}` arity mismatch between `{}` ({}) and `{}` ({})",
                        t_obs.name,
                        sc.after_phase.name,
                        s_obs.components.len(),
                        t_ph.name,
                        t_obs.components.len()
                    ),
                ))
                .into());
            }
        }
        scs.push(ShigureStateComparison {
            after_phase: sc.after_phase.name.clone(),
            before_phase: sc.before_phase.name.clone(),
            map,
            span: sc.span,
        });
    }
    if phase_map.len() != src_pres.phases.len() {
        return Err(Box::new(Issue::law(
            Code::Type,
            span,
            format!(
                "{context} must define a `state_map` for every phase of `{}`",
                src_pres.name
            ),
        ))
        .into());
    }

    let mut seen_ops = HashSet::new();
    let mut wt = Vec::with_capacity(raw_wt.len());
    for tw in raw_wt {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        let Some(s_op) = src_pres
            .operations
            .iter()
            .find(|o| o.name == tw.after_operation.name)
        else {
            return reference(
                tw.after_operation.span,
                format!(
                    "unknown operation `{}` on `{}` ({context})",
                    tw.after_operation.name, src_pres.name
                ),
            );
        };
        if !seen_ops.insert(tw.after_operation.name.clone()) {
            return duplicate(
                tw.after_operation.span,
                format!(
                    "duplicate translate entry for `{}` in {context}",
                    tw.after_operation.name
                ),
            );
        }
        let expected_src = &phase_map[&s_op.source_phase];
        let expected_dst = &phase_map[&s_op.target_phase];
        let mut steps = Vec::with_capacity(tw.steps.len());
        if tw.steps.is_empty() {
            if expected_src != expected_dst {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    tw.span,
                    format!(
                        "empty translation for `{}` requires h({}) == h({}) (got `{expected_src}` vs `{expected_dst}`)",
                        s_op.name, s_op.source_phase, s_op.target_phase
                    ),
                ))
                .into());
            }
        } else {
            let mut cur_phase = expected_src.as_str();
            for st in &tw.steps {
                E::checkpoint(control, Checkpoint::LawSemantics)?;
                let Some(t_op) = tgt_pres
                    .operations
                    .iter()
                    .find(|o| o.name == st.before_operation.name)
                else {
                    return reference(
                        st.before_operation.span,
                        format!(
                            "unknown target operation `{}` in {context}",
                            st.before_operation.name
                        ),
                    );
                };
                if t_op.source_phase != cur_phase {
                    return Err(Box::new(Issue::law(
                        Code::Type,
                        st.span,
                        format!(
                            "translated step `{}` starts at phase `{}`, expected `{cur_phase}`",
                            t_op.name, t_op.source_phase
                        ),
                    ))
                    .into());
                }
                if st.arg_exprs.len() != t_op.args.len() {
                    return Err(Box::new(Issue::law(
                        Code::Type,
                        st.span,
                        format!(
                            "translated step `{}` expects {} arguments, got {}",
                            t_op.name,
                            t_op.args.len(),
                            st.arg_exprs.len()
                        ),
                    ))
                    .into());
                }
                for e in &st.arg_exprs {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    check_poly_literals(
                        e,
                        LiteralDomainRule::Exact(&src_pres.coeff_domain),
                        st.span,
                        control,
                    )?;
                }
                cur_phase = t_op.target_phase.as_str();
                steps.push(ShigureTranslatedStep {
                    before_operation: st.before_operation.name.clone(),
                    arg_exprs: st.arg_exprs.clone(),
                    span: st.span,
                });
            }
            if cur_phase != expected_dst.as_str() {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    tw.span,
                    format!(
                        "translated word for `{}` ends at phase `{cur_phase}`, expected `{expected_dst}`",
                        s_op.name
                    ),
                ))
                .into());
            }
        }
        wt.push(ShigureTranslatedWord {
            after_operation: tw.after_operation.name.clone(),
            steps,
            span: tw.span,
        });
    }
    if seen_ops.len() != src_pres.operations.len() {
        return Err(Box::new(Issue::law(
            Code::Type,
            span,
            format!(
                "{context} must define a `translate` entry for every operation of `{}`",
                src_pres.name
            ),
        ))
        .into());
    }
    Ok((scs, wt))
}

pub(super) fn check_morphism_vars_against_pres<E: InputError>(
    scs: &[ShigureStateComparison],
    wt: &[ShigureTranslatedWord],
    src_pres: &ShigurePresentation,
    params: Option<&HashSet<&str>>,
    context: &str,
    span: Span,
    control: &Control,
) -> CResult<(), E> {
    for sc in scs {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        let src_ph = src_pres
            .phases
            .iter()
            .find(|p| p.name == sc.after_phase)
            .expect("checked src_phase");
        let mut allowed: HashSet<&str> = src_ph.coords.iter().map(|c| c.name.as_str()).collect();
        if let Some(ps) = params {
            check_coords_disjoint_from_params(
                &src_ph.coords,
                ps,
                &src_pres.name,
                &src_ph.name,
                context,
                control,
            )?;
            allowed.extend(ps.iter().copied());
        }
        for (coord, expr) in &sc.map {
            let ctx = format!("{context}.state_map.{}.{coord}", sc.after_phase);
            check_poly_vars(expr, &allowed, span, &ctx, control)?;
        }
    }
    for tw in wt {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        let src_op = src_pres
            .operations
            .iter()
            .find(|o| o.name == tw.after_operation)
            .expect("checked src_operation");
        let src_ph = src_pres
            .phases
            .iter()
            .find(|p| p.name == src_op.source_phase)
            .expect("checked src_op.source_phase");
        let mut allowed: HashSet<&str> = src_ph.coords.iter().map(|c| c.name.as_str()).collect();
        allowed.extend(src_op.args.iter().map(|(a, _)| a.as_str()));
        if let Some(ps) = params {
            check_coords_disjoint_from_params(
                &src_ph.coords,
                ps,
                &src_pres.name,
                &src_ph.name,
                context,
                control,
            )?;
            for (a_name, _) in &src_op.args {
                E::checkpoint(control, Checkpoint::LawSemantics)?;
                if ps.contains(a_name.as_str()) {
                    return duplicate(
                        src_op.span,
                        format!(
                            "argument `{a_name}` in `{}.{}` collides with change_spec parameter in {context}",
                            src_pres.name, src_op.name
                        ),
                    );
                }
            }
            allowed.extend(ps.iter().copied());
        }
        for st in &tw.steps {
            for (idx, expr) in st.arg_exprs.iter().enumerate() {
                let ctx = format!(
                    "{context}.translate.{}.{}[{idx}]",
                    tw.after_operation, st.before_operation
                );
                check_poly_vars(expr, &allowed, st.span, &ctx, control)?;
            }
        }
    }
    Ok(())
}
