//! `shigure comparison` / `change_spec` / `eval_condition` / `task` の静的検査。

use super::check::{
    CResult, DeclCategory, check_coeff_domain, check_point_domain, check_poly_literals,
    resolve_shigure_ref,
};
use super::*;
use crate::law::ast::{QName, Span};
use crate::law::check::{Checker, duplicate, full, reference, syntax};
use archsig_common::control::Control;
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

    let mut seen_phases = HashSet::new();
    let mut state_comparisons = Vec::with_capacity(raw.state_comparisons.len());
    for sc in &raw.state_comparisons {
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
        if !seen_phases.insert(sc.after_phase.name.clone()) {
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
            check_poly_literals(expr, Some(&before_p.coeff_domain), sc.span, control)?;
            map.push((coord.name.clone(), expr.clone()));
        }
        state_comparisons.push(ShigureStateComparison {
            after_phase: sc.after_phase.name.clone(),
            before_phase: sc.before_phase.name.clone(),
            map,
            span: sc.span,
        });
    }

    let mut seen_ops = HashSet::new();
    let mut word_translation = Vec::with_capacity(raw.word_translation.len());
    for tw in &raw.word_translation {
        if !after_p
            .operations
            .iter()
            .any(|o| o.name == tw.after_operation.name)
        {
            return reference(
                tw.after_operation.span,
                format!("unknown after operation `{}`", tw.after_operation.name),
            );
        }
        if !seen_ops.insert(tw.after_operation.name.clone()) {
            return duplicate(
                tw.after_operation.span,
                format!(
                    "duplicate translate entry for `{}`",
                    tw.after_operation.name
                ),
            );
        }
        let mut steps = Vec::with_capacity(tw.steps.len());
        for st in &tw.steps {
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
                check_poly_literals(e, Some(&before_p.coeff_domain), st.span, control)?;
            }
            steps.push(ShigureTranslatedStep {
                before_operation: st.before_operation.name.clone(),
                arg_exprs: st.arg_exprs.clone(),
                span: st.span,
            });
        }
        word_translation.push(ShigureTranslatedWord {
            after_operation: tw.after_operation.name.clone(),
            steps,
            span: tw.span,
        });
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
        for (f, _) in &fixed {
            if editable_conflicts_with_fixed(&resolved, f) {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    *span,
                    "target cannot be both `fixed` and `editable`",
                ))
                .into());
            }
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

fn editable_conflicts_with_fixed(e: &ShigureEditableTarget, f: &ShigureFixedTarget) -> bool {
    match (e, f) {
        (
            ShigureEditableTarget::OperationExpr {
                presentation: p1,
                operation: o1,
            },
            ShigureFixedTarget::OperationExpr {
                presentation: p2,
                operation: o2,
            },
        ) => p1 == p2 && o1 == o2,
        (
            ShigureEditableTarget::RepresentationLaw {
                presentation: p1,
                phase: ph1,
                law: l1,
            },
            ShigureFixedTarget::RepresentationLaw {
                presentation: p2,
                phase: ph2,
                law: l2,
            },
        ) => p1 == p2 && ph1 == ph2 && l1 == l2,
        (
            ShigureEditableTarget::StateComparisonExpr { after_phase: a1 },
            ShigureFixedTarget::StateComparisonExpr { after_phase: a2 },
        ) => a1 == a2,
        _ => false,
    }
}

pub(super) fn check_eval_condition<E: InputError>(
    raw: &RawEvalCondition,
    reading_name: &str,
    control: &Control,
) -> CResult<ShigureEvalCondition, E> {
    let full_name = full(reading_name, &[&raw.name.name]);
    let point_domain = check_point_domain(&raw.point_domain, control)?;
    let literal_domain = match &point_domain {
        ShigurePointDomain::FiniteFieldPoints(p) => Some(ShigureCoeffDomain::Fp(p.clone())),
        _ => None,
    };

    let check_list = |items: &[RawNamedPoly], kind: &str| -> CResult<Vec<ShigureNamedPoly>, E> {
        let mut seen = HashSet::new();
        let mut out = Vec::with_capacity(items.len());
        for item in items {
            if !seen.insert(item.name.name.clone()) {
                return duplicate(
                    item.name.span,
                    format!("duplicate {kind} name `{}`", item.name.name),
                );
            }
            check_poly_literals(&item.expr, literal_domain.as_ref(), item.span, control)?;
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

pub(super) fn check_task<E: InputError>(
    raw: &RawTask,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span)>,
    decls: &CheckedShigureDecls,
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
