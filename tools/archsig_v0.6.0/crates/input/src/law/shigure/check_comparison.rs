//! `shigure comparison` の静的検査と `change_spec` との整合検査。

use super::check::{
    CResult, DeclCategory, LiteralDomainRule, ShigureDeclCtx, check_poly_literals, check_poly_vars,
    check_presentation_vars,
};
use super::*;
use crate::law::check::{duplicate, reference};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;
use std::collections::{HashMap, HashSet};

pub(super) fn check_comparison<E: InputError>(
    raw: &RawComparison,
    ctx: &mut ShigureDeclCtx<'_, '_, E>,
) -> CResult<ShigureComparison, E> {
    let full_name = ctx.full_name(&raw.name.name);
    let before = ctx.resolve_ref(&raw.before, DeclCategory::Presentation)?;
    let after = ctx.resolve_ref(&raw.after, DeclCategory::Presentation)?;
    if before == after {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw.span,
            "`before` and `after` presentations must be distinct",
        ))
        .into());
    }
    let before_p = &ctx.decls.presentations[&before];
    let after_p = &ctx.decls.presentations[&after];
    let control = ctx.control;
    if before_p.coeff_domain != after_p.coeff_domain {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw.span,
            "`before` and `after` presentations must share the same coefficient domain",
        ))
        .into());
    }
    // `before` 表示は探索パラメータ禁止であり、全式の変数が座標・引数のみで閉じることを確定検査する。
    check_presentation_vars(before_p, None, control)?;

    let mut phase_map: HashMap<String, String> = HashMap::new();
    let mut state_comparisons = Vec::with_capacity(raw.state_comparisons.len());
    for sc in &raw.state_comparisons {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !after_p.phases.iter().any(|p| p.name == sc.after_phase.name) {
            return reference(
                sc.after_phase.span,
                format!("unknown after phase `{}`", sc.after_phase.name),
            );
        }
        let Some(b_phase) = before_p
            .phases
            .iter()
            .find(|p| p.name == sc.before_phase.name)
        else {
            return reference(
                sc.before_phase.span,
                format!("unknown before phase `{}`", sc.before_phase.name),
            );
        };
        if phase_map
            .insert(sc.after_phase.name.clone(), sc.before_phase.name.clone())
            .is_some()
        {
            return duplicate(
                sc.after_phase.span,
                format!(
                    "duplicate state_map for after phase `{}`",
                    sc.after_phase.name
                ),
            );
        }
        let mut seen_coords = HashSet::new();
        let mut map = Vec::with_capacity(sc.map.len());
        for (coord, expr) in &sc.map {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            if !b_phase.coords.iter().any(|c| c.name == coord.name) {
                return reference(
                    coord.span,
                    format!(
                        "unknown before coordinate `{}` in phase `{}`",
                        coord.name, b_phase.name
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
                LiteralDomainRule::Exact(&before_p.coeff_domain),
                sc.span,
                control,
            )?;
            map.push((coord.name.clone(), expr.clone()));
        }
        if seen_coords.len() != b_phase.coords.len() {
            return Err(Box::new(Issue::law(
                Code::Type,
                sc.span,
                format!(
                    "state_map `{}` -> `{}` must assign every coordinate of before phase `{}`",
                    sc.after_phase.name, b_phase.name, b_phase.name
                ),
            ))
            .into());
        }
        // before phase の各観測が after phase に同名・同成分数で存在することを検査する。
        for b_obs in before_p
            .observations
            .iter()
            .filter(|o| o.phase == b_phase.name)
        {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            let Some(a_obs) = after_p
                .observations
                .iter()
                .find(|o| o.phase == sc.after_phase.name && o.name == b_obs.name)
            else {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    sc.span,
                    format!(
                        "after phase `{}` is missing observation `{}` required by before phase `{}`",
                        sc.after_phase.name, b_obs.name, b_phase.name
                    ),
                ))
                .into());
            };
            if a_obs.components.len() != b_obs.components.len() {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    sc.span,
                    format!(
                        "observation `{}` arity mismatch between after phase `{}` ({}) and before phase `{}` ({})",
                        b_obs.name,
                        sc.after_phase.name,
                        a_obs.components.len(),
                        b_phase.name,
                        b_obs.components.len()
                    ),
                ))
                .into());
            }
        }
        state_comparisons.push(ShigureStateComparison {
            after_phase: sc.after_phase.name.clone(),
            before_phase: sc.before_phase.name.clone(),
            map,
            span: sc.span,
        });
    }
    if phase_map.len() != after_p.phases.len() {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw.span,
            format!(
                "`shigure comparison {}` must define a `state_map` for every phase of `{}`",
                raw.name.name, after_p.name
            ),
        ))
        .into());
    }

    let mut seen_ops = HashSet::new();
    let mut word_translation = Vec::with_capacity(raw.word_translation.len());
    for tw in &raw.word_translation {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        let Some(after_op) = after_p
            .operations
            .iter()
            .find(|o| o.name == tw.after_operation.name)
        else {
            return reference(
                tw.after_operation.span,
                format!("unknown after operation `{}`", tw.after_operation.name),
            );
        };
        if !seen_ops.insert(tw.after_operation.name.clone()) {
            return duplicate(
                tw.after_operation.span,
                format!(
                    "duplicate translate entry for `{}`",
                    tw.after_operation.name
                ),
            );
        }
        let expected_src = &phase_map[&after_op.source_phase];
        let expected_dst = &phase_map[&after_op.target_phase];
        let mut steps = Vec::with_capacity(tw.steps.len());
        if tw.steps.is_empty() {
            if expected_src != expected_dst {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    tw.span,
                    format!(
                        "empty translation for `{}` requires h({}) == h({}) (got `{expected_src}` vs `{expected_dst}`)",
                        after_op.name, after_op.source_phase, after_op.target_phase
                    ),
                ))
                .into());
            }
        } else {
            let mut cur_phase = expected_src.as_str();
            for st in &tw.steps {
                E::checkpoint(control, Checkpoint::LawSemantics)?;
                let Some(b_op) = before_p
                    .operations
                    .iter()
                    .find(|o| o.name == st.before_operation.name)
                else {
                    return reference(
                        st.before_operation.span,
                        format!("unknown before operation `{}`", st.before_operation.name),
                    );
                };
                if b_op.source_phase != cur_phase {
                    return Err(Box::new(Issue::law(
                        Code::Type,
                        st.span,
                        format!(
                            "translated step `{}` starts at phase `{}`, expected `{cur_phase}`",
                            b_op.name, b_op.source_phase
                        ),
                    ))
                    .into());
                }
                if st.arg_exprs.len() != b_op.args.len() {
                    return Err(Box::new(Issue::law(
                        Code::Type,
                        st.span,
                        format!(
                            "translated step `{}` expects {} arguments, got {}",
                            b_op.name,
                            b_op.args.len(),
                            st.arg_exprs.len()
                        ),
                    ))
                    .into());
                }
                for e in &st.arg_exprs {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    check_poly_literals(
                        e,
                        LiteralDomainRule::Exact(&before_p.coeff_domain),
                        st.span,
                        control,
                    )?;
                }
                cur_phase = b_op.target_phase.as_str();
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
                        after_op.name
                    ),
                ))
                .into());
            }
        }
        word_translation.push(ShigureTranslatedWord {
            after_operation: tw.after_operation.name.clone(),
            steps,
            span: tw.span,
        });
    }
    if seen_ops.len() != after_p.operations.len() {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw.span,
            format!(
                "`shigure comparison {}` must define a `translate` entry for every operation of `{}`",
                raw.name.name, after_p.name
            ),
        ))
        .into());
    }

    Ok(ShigureComparison {
        name: full_name,
        reading: ctx.reading_name.to_owned(),
        before,
        after,
        state_comparisons,
        word_translation,
        span: raw.span,
    })
}

pub(super) fn check_comparison_against_change_spec<E: InputError>(
    cmp: &ShigureComparison,
    after_p: &ShigurePresentation,
    spec: &ShigureChangeSpec,
    control: &Control,
) -> CResult<(), E> {
    for (target, span) in &spec.fixed {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        match target {
            ShigureFixedTarget::SemanticLaw { presentation, .. }
            | ShigureFixedTarget::RepresentationLaw { presentation, .. }
            | ShigureFixedTarget::OperationExpr { presentation, .. }
            | ShigureFixedTarget::ObservationExpr { presentation, .. } => {
                if presentation != &cmp.before && presentation != &cmp.after {
                    return reference(
                        *span,
                        format!(
                            "fixed target references presentation `{presentation}` outside comparison `{}`",
                            cmp.name
                        ),
                    );
                }
            }
            ShigureFixedTarget::StateComparisonExpr { after_phase } => {
                if !after_p.phases.iter().any(|p| p.name == *after_phase) {
                    return reference(
                        *span,
                        format!(
                            "fixed state_comparison references unknown after phase `{after_phase}`"
                        ),
                    );
                }
            }
            ShigureFixedTarget::WordTranslationOp { operation } => {
                if !after_p.operations.iter().any(|o| o.name == *operation) {
                    return reference(
                        *span,
                        format!(
                            "fixed word_translation references unknown after operation `{operation}`"
                        ),
                    );
                }
            }
        }
    }
    for (target, span) in &spec.editable {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        match target {
            ShigureEditableTarget::OperationExpr { presentation, .. }
            | ShigureEditableTarget::RepresentationLaw { presentation, .. } => {
                if presentation != &cmp.after {
                    return Err(Box::new(Issue::law(
                        Code::Type,
                        *span,
                        format!(
                            "editable target must belong to `after` presentation `{}` (got `{presentation}`)",
                            cmp.after
                        ),
                    ))
                    .into());
                }
            }
            ShigureEditableTarget::StateComparisonExpr { after_phase } => {
                if !after_p.phases.iter().any(|p| p.name == *after_phase) {
                    return reference(
                        *span,
                        format!(
                            "editable state_comparison references unknown after phase `{after_phase}`"
                        ),
                    );
                }
            }
        }
    }
    let param_set: HashSet<&str> = spec.parameters.iter().map(|p| p.name.as_str()).collect();
    check_presentation_vars(after_p, Some(&param_set), control)?;
    for sc in &cmp.state_comparisons {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        let after_ph = after_p
            .phases
            .iter()
            .find(|p| p.name == sc.after_phase)
            .expect("checked after_phase");
        let mut allowed: HashSet<&str> = after_ph.coords.iter().map(|c| c.name.as_str()).collect();
        allowed.extend(param_set.iter().copied());
        for (coord, expr) in &sc.map {
            let ctx = format!("{}.state_map.{}.{coord}", cmp.name, sc.after_phase);
            check_poly_vars(expr, &allowed, sc.span, &ctx, control)?;
        }
    }
    for tw in &cmp.word_translation {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        let after_op = after_p
            .operations
            .iter()
            .find(|o| o.name == tw.after_operation)
            .expect("checked after_operation");
        let src_ph = after_p
            .phases
            .iter()
            .find(|p| p.name == after_op.source_phase)
            .expect("checked source_phase");
        let mut allowed: HashSet<&str> = src_ph.coords.iter().map(|c| c.name.as_str()).collect();
        allowed.extend(after_op.args.iter().map(|(a, _)| a.as_str()));
        allowed.extend(param_set.iter().copied());
        for st in &tw.steps {
            for (idx, expr) in st.arg_exprs.iter().enumerate() {
                let ctx = format!(
                    "{}.translate.{}.{}[{idx}]",
                    cmp.name, tw.after_operation, st.before_operation
                );
                check_poly_vars(expr, &allowed, st.span, &ctx, control)?;
            }
        }
    }
    Ok(())
}
