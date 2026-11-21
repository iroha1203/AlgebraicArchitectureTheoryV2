//! `shigure comparison` / `change_spec` / `eval_condition` / `task` の静的検査。

use super::check::{
    CResult, DeclCategory, LiteralDomainRule, check_coeff_domain, check_point_domain,
    check_poly_literals, resolve_shigure_ref,
};
use super::*;
use crate::law::ast::{QName, Span};
use crate::law::check::{Checker, duplicate, full, reference, syntax};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;
use std::collections::{BTreeMap, HashMap, HashSet};

pub(super) fn check_comparison<E: InputError>(
    raw: &RawComparison,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span)>,
    presentations: &BTreeMap<String, ShigurePresentation>,
    control: &Control,
) -> CResult<ShigureComparison, E> {
    let full_name = full(reading_name, &[&raw.name.name]);
    let before = resolve_shigure_ref(
        &raw.before,
        DeclCategory::Presentation,
        r_idx,
        reading_name,
        checker,
        index,
    )?;
    let after = resolve_shigure_ref(
        &raw.after,
        DeclCategory::Presentation,
        r_idx,
        reading_name,
        checker,
        index,
    )?;
    if before == after {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw.span,
            "`before` and `after` presentations must be distinct",
        ))
        .into());
    }
    let before_p = &presentations[&before];
    let after_p = &presentations[&after];
    if before_p.coeff_domain != after_p.coeff_domain {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw.span,
            "`before` and `after` presentations must share the same coefficient domain",
        ))
        .into());
    }

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
        reading: reading_name.to_owned(),
        before,
        after,
        state_comparisons,
        word_translation,
        span: raw.span,
    })
}

fn split_pres_tail<E: InputError>(
    qname: &QName,
    tail_len: usize,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span)>,
) -> CResult<(String, Vec<String>), E> {
    if qname.parts.len() <= tail_len {
        return syntax(
            qname.span(),
            format!(
                "target `{}` must include presentation prefix and {} member name(s)",
                qname.text(),
                tail_len
            ),
        );
    }
    let split_at = qname.parts.len() - tail_len;
    let pres_qname = QName {
        parts: qname.parts[..split_at].to_vec(),
    };
    let pres = resolve_shigure_ref(
        &pres_qname,
        DeclCategory::Presentation,
        r_idx,
        reading_name,
        checker,
        index,
    )?;
    let tail = qname.parts[split_at..]
        .iter()
        .map(|p| p.name.clone())
        .collect();
    Ok((pres, tail))
}

pub(super) fn check_change_spec<E: InputError>(
    raw: &RawChangeSpec,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span)>,
    presentations: &BTreeMap<String, ShigurePresentation>,
    control: &Control,
) -> CResult<ShigureChangeSpec, E> {
    let full_name = full(reading_name, &[&raw.name.name]);
    let coeff_domain = check_coeff_domain(&raw.domain, control)?;

    let mut seen_params = HashSet::new();
    let mut parameters = Vec::with_capacity(raw.parameters.len());
    for p in &raw.parameters {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !seen_params.insert(p.name.name.clone()) {
            return duplicate(
                p.name.span,
                format!("duplicate parameter `{}`", p.name.name),
            );
        }
        let p_dom = check_coeff_domain(&p.domain, control)?;
        if p_dom != coeff_domain {
            return Err(Box::new(Issue::law(
                Code::Type,
                p.span,
                format!(
                    "parameter `{}` domain must match change_spec domain",
                    p.name.name
                ),
            ))
            .into());
        }
        parameters.push(ShigureParamDecl {
            name: p.name.name.clone(),
            coeff_domain: p_dom,
            span: p.span,
        });
    }

    let mut seen_fixed = HashSet::new();
    let mut fixed = Vec::with_capacity(raw.fixed.len());
    for (target, span) in &raw.fixed {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        let resolved = match target {
            RawFixedTarget::SemanticLaw(q) => {
                let (pres, tail) = split_pres_tail(q, 2, r_idx, reading_name, checker, index)?;
                validate_law_target(
                    presentations,
                    &pres,
                    &tail[0],
                    &tail[1],
                    ShigureLawKind::Semantic,
                    *span,
                )?;
                ShigureFixedTarget::SemanticLaw {
                    presentation: pres,
                    phase: tail[0].clone(),
                    law: tail[1].clone(),
                }
            }
            RawFixedTarget::RepresentationLaw(q) => {
                let (pres, tail) = split_pres_tail(q, 2, r_idx, reading_name, checker, index)?;
                validate_law_target(
                    presentations,
                    &pres,
                    &tail[0],
                    &tail[1],
                    ShigureLawKind::Representation,
                    *span,
                )?;
                ShigureFixedTarget::RepresentationLaw {
                    presentation: pres,
                    phase: tail[0].clone(),
                    law: tail[1].clone(),
                }
            }
            RawFixedTarget::OperationExpr(q) => {
                let (pres, tail) = split_pres_tail(q, 1, r_idx, reading_name, checker, index)?;
                if !presentations[&pres]
                    .operations
                    .iter()
                    .any(|o| o.name == tail[0])
                {
                    return reference(
                        *span,
                        format!("unknown operation `{}` on `{pres}`", tail[0]),
                    );
                }
                ShigureFixedTarget::OperationExpr {
                    presentation: pres,
                    operation: tail[0].clone(),
                }
            }
            RawFixedTarget::ObservationExpr(q) => {
                let (pres, tail) = split_pres_tail(q, 2, r_idx, reading_name, checker, index)?;
                if !presentations[&pres]
                    .observations
                    .iter()
                    .any(|o| o.phase == tail[0] && o.name == tail[1])
                {
                    return reference(
                        *span,
                        format!("unknown observation `{}.{}` on `{pres}`", tail[0], tail[1]),
                    );
                }
                ShigureFixedTarget::ObservationExpr {
                    presentation: pres,
                    phase: tail[0].clone(),
                    observation: tail[1].clone(),
                }
            }
            RawFixedTarget::StateComparisonExpr(id) => ShigureFixedTarget::StateComparisonExpr {
                after_phase: id.name.clone(),
            },
            RawFixedTarget::WordTranslationOp(id) => ShigureFixedTarget::WordTranslationOp {
                operation: id.name.clone(),
            },
        };
        if !seen_fixed.insert(resolved.clone()) {
            return duplicate(*span, "duplicate `fixed` target in `shigure change_spec`");
        }
        fixed.push((resolved, *span));
    }

    let mut seen_editable = HashSet::new();
    let mut editable = Vec::with_capacity(raw.editable.len());
    for (target, span) in &raw.editable {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        let resolved = match target {
            RawEditableTarget::OperationExpr(q) => {
                let (pres, tail) = split_pres_tail(q, 1, r_idx, reading_name, checker, index)?;
                if !presentations[&pres]
                    .operations
                    .iter()
                    .any(|o| o.name == tail[0])
                {
                    return reference(
                        *span,
                        format!("unknown operation `{}` on `{pres}`", tail[0]),
                    );
                }
                ShigureEditableTarget::OperationExpr {
                    presentation: pres,
                    operation: tail[0].clone(),
                }
            }
            RawEditableTarget::RepresentationLaw(q) => {
                let (pres, tail) = split_pres_tail(q, 2, r_idx, reading_name, checker, index)?;
                validate_law_target(
                    presentations,
                    &pres,
                    &tail[0],
                    &tail[1],
                    ShigureLawKind::Representation,
                    *span,
                )?;
                ShigureEditableTarget::RepresentationLaw {
                    presentation: pres,
                    phase: tail[0].clone(),
                    law: tail[1].clone(),
                }
            }
            RawEditableTarget::StateComparisonExpr(id) => {
                ShigureEditableTarget::StateComparisonExpr {
                    after_phase: id.name.clone(),
                }
            }
        };
        if !seen_editable.insert(resolved.clone()) {
            return duplicate(
                *span,
                "duplicate `editable` target in `shigure change_spec`",
            );
        }
        if seen_fixed.contains(&editable_fixed_counterpart(&resolved)) {
            return Err(Box::new(Issue::law(
                Code::Type,
                *span,
                "target cannot be both `fixed` and `editable`",
            ))
            .into());
        }
        editable.push((resolved, *span));
    }

    Ok(ShigureChangeSpec {
        name: full_name,
        reading: reading_name.to_owned(),
        coeff_domain,
        parameters,
        fixed,
        editable,
        span: raw.span,
    })
}

fn validate_law_target<E: InputError>(
    presentations: &BTreeMap<String, ShigurePresentation>,
    pres: &str,
    phase: &str,
    law: &str,
    expected_kind: ShigureLawKind,
    span: Span,
) -> CResult<(), E> {
    let Some(ph) = presentations[pres].phases.iter().find(|p| p.name == phase) else {
        return reference(span, format!("unknown phase `{phase}` on `{pres}`"));
    };
    let Some(l) = ph.state_laws.iter().find(|l| l.name == law) else {
        return reference(
            span,
            format!("unknown state law `{law}` on `{pres}.{phase}`"),
        );
    };
    if l.kind != expected_kind {
        return Err(Box::new(Issue::law(
            Code::Type,
            span,
            format!("state law `{pres}.{phase}.{law}` does not have expected kind"),
        ))
        .into());
    }
    Ok(())
}

fn editable_fixed_counterpart(e: &ShigureEditableTarget) -> ShigureFixedTarget {
    match e {
        ShigureEditableTarget::OperationExpr {
            presentation,
            operation,
        } => ShigureFixedTarget::OperationExpr {
            presentation: presentation.clone(),
            operation: operation.clone(),
        },
        ShigureEditableTarget::RepresentationLaw {
            presentation,
            phase,
            law,
        } => ShigureFixedTarget::RepresentationLaw {
            presentation: presentation.clone(),
            phase: phase.clone(),
            law: law.clone(),
        },
        ShigureEditableTarget::StateComparisonExpr { after_phase } => {
            ShigureFixedTarget::StateComparisonExpr {
                after_phase: after_phase.clone(),
            }
        }
    }
}

pub(super) fn check_eval_condition<E: InputError>(
    raw: &RawEvalCondition,
    reading_name: &str,
    control: &Control,
) -> CResult<ShigureEvalCondition, E> {
    let full_name = full(reading_name, &[&raw.name.name]);
    let point_domain = check_point_domain(&raw.point_domain, control)?;
    let fp_domain_owned = match &point_domain {
        ShigurePointDomain::FiniteFieldPoints(p) => Some(ShigureCoeffDomain::Fp(p.clone())),
        _ => None,
    };
    let z_domain = ShigureCoeffDomain::Z;
    let literal_rule = match &point_domain {
        ShigurePointDomain::IntegerPoints => LiteralDomainRule::Exact(&z_domain),
        ShigurePointDomain::FiniteFieldPoints(_) => {
            LiteralDomainRule::Exact(fp_domain_owned.as_ref().expect("fp domain"))
        }
        ShigurePointDomain::AlgebraicClosure | ShigurePointDomain::RationalPoints => {
            LiteralDomainRule::NonFp
        }
        ShigurePointDomain::UniversalRing => LiteralDomainRule::Any,
    };

    let check_list = |items: &[RawNamedPoly], kind: &str| -> CResult<Vec<ShigureNamedPoly>, E> {
        let mut seen = HashSet::new();
        let mut out = Vec::with_capacity(items.len());
        for item in items {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            if !seen.insert(item.name.name.clone()) {
                return duplicate(
                    item.name.span,
                    format!("duplicate {kind} name `{}`", item.name.name),
                );
            }
            check_poly_literals(&item.expr, literal_rule.clone(), item.span, control)?;
            out.push(ShigureNamedPoly {
                name: item.name.name.clone(),
                expr: item.expr.clone(),
                span: item.span,
            });
        }
        Ok(out)
    };

    let evaluations = check_list(&raw.evaluations, "eval")?;
    let equations = check_list(&raw.equations, "equation")?;
    let invertibles = check_list(&raw.invertibles, "invertible")?;

    Ok(ShigureEvalCondition {
        name: full_name,
        reading: reading_name.to_owned(),
        point_domain,
        evaluations,
        equations,
        invertibles,
        span: raw.span,
    })
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_task<E: InputError>(
    raw: &RawTask,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span)>,
    decls: &CheckedShigureDecls,
    control: &Control,
) -> CResult<ShigureTask, E> {
    let full_name = full(reading_name, &[&raw.name.name]);
    let comparison = resolve_shigure_ref(
        &raw.comparison,
        DeclCategory::Comparison,
        r_idx,
        reading_name,
        checker,
        index,
    )?;
    let change_spec = resolve_shigure_ref(
        &raw.change_spec,
        DeclCategory::ChangeSpec,
        r_idx,
        reading_name,
        checker,
        index,
    )?;
    let eval_condition = match &raw.eval_condition {
        Some(q) => Some(resolve_shigure_ref(
            q,
            DeclCategory::EvalCondition,
            r_idx,
            reading_name,
            checker,
            index,
        )?),
        None => None,
    };

    let cmp = &decls.comparisons[&comparison];
    let spec = &decls.change_specs[&change_spec];
    let before_p = &decls.presentations[&cmp.before];
    let after_p = &decls.presentations[&cmp.after];
    if spec.coeff_domain != before_p.coeff_domain {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw.span,
            "`change_spec` coefficient domain must match `comparison` presentations",
        ))
        .into());
    }
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
                            "fixed target references presentation `{presentation}` outside comparison `{comparison}`"
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
    if let Some(ec_name) = &eval_condition {
        let ec = &decls.eval_conditions[ec_name];
        let compatible = match (&spec.coeff_domain, &ec.point_domain) {
            (ShigureCoeffDomain::Q, ShigurePointDomain::AlgebraicClosure)
            | (ShigureCoeffDomain::Q, ShigurePointDomain::RationalPoints)
            | (ShigureCoeffDomain::Q, ShigurePointDomain::UniversalRing)
            | (ShigureCoeffDomain::Z, ShigurePointDomain::AlgebraicClosure)
            | (ShigureCoeffDomain::Z, ShigurePointDomain::RationalPoints)
            | (ShigureCoeffDomain::Z, ShigurePointDomain::IntegerPoints)
            | (ShigureCoeffDomain::Z, ShigurePointDomain::UniversalRing) => true,
            (ShigureCoeffDomain::Fp(p1), ShigurePointDomain::FiniteFieldPoints(p2)) => p1 == p2,
            (ShigureCoeffDomain::Fp(_), ShigurePointDomain::UniversalRing) => true,
            _ => false,
        };
        if !compatible {
            return Err(Box::new(Issue::law(
                Code::Type,
                raw.span,
                "`eval_condition` point_domain is incompatible with `change_spec` coefficient domain",
            ))
            .into());
        }
        for item in ec
            .evaluations
            .iter()
            .chain(&ec.equations)
            .chain(&ec.invertibles)
        {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            check_poly_literals(
                &item.expr,
                LiteralDomainRule::Exact(&spec.coeff_domain),
                item.span,
                control,
            )?;
        }
    }

    Ok(ShigureTask {
        name: full_name,
        reading: reading_name.to_owned(),
        comparison,
        change_spec,
        eval_condition,
        span: raw.span,
    })
}
