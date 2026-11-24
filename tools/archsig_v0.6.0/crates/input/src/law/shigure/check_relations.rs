//! `shigure change_spec` / `eval_condition` / `task` の静的検査。

use super::check::{
    CResult, DeclCategory, LiteralDomainRule, check_coeff_domain, check_point_domain,
    check_poly_literals, check_poly_vars, resolve_shigure_ref,
};
pub(super) use super::check_comparison::check_comparison_against_change_spec;
use super::*;
use crate::law::ast::{QName, Span};
use crate::law::check::{Checker, duplicate, full, reference, syntax};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;
use std::collections::{BTreeMap, HashMap, HashSet};

fn split_pres_tail<E: InputError>(
    qname: &QName,
    tail_len: usize,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span, usize)>,
    edges: &mut Vec<(usize, usize, Span)>,
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
        edges,
    )?;
    let tail = qname.parts[split_at..]
        .iter()
        .map(|p| p.name.clone())
        .collect();
    Ok((pres, tail))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_change_spec<E: InputError>(
    raw: &RawChangeSpec,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span, usize)>,
    presentations: &BTreeMap<String, ShigurePresentation>,
    edges: &mut Vec<(usize, usize, Span)>,
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
                let (pres, tail) =
                    split_pres_tail(q, 2, r_idx, reading_name, checker, index, edges)?;
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
                let (pres, tail) =
                    split_pres_tail(q, 2, r_idx, reading_name, checker, index, edges)?;
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
                let (pres, tail) =
                    split_pres_tail(q, 1, r_idx, reading_name, checker, index, edges)?;
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
                let (pres, tail) =
                    split_pres_tail(q, 2, r_idx, reading_name, checker, index, edges)?;
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
                let (pres, tail) =
                    split_pres_tail(q, 1, r_idx, reading_name, checker, index, edges)?;
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
                let (pres, tail) =
                    split_pres_tail(q, 2, r_idx, reading_name, checker, index, edges)?;
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
    index: &HashMap<String, (DeclCategory, Span, usize)>,
    decls: &CheckedShigureDecls,
    edges: &mut Vec<(usize, usize, Span)>,
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
        edges,
    )?;
    let change_spec = resolve_shigure_ref(
        &raw.change_spec,
        DeclCategory::ChangeSpec,
        r_idx,
        reading_name,
        checker,
        index,
        edges,
    )?;
    let eval_condition = match &raw.eval_condition {
        Some(q) => Some(resolve_shigure_ref(
            q,
            DeclCategory::EvalCondition,
            r_idx,
            reading_name,
            checker,
            index,
            edges,
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
    check_comparison_against_change_spec(cmp, after_p, spec, control)?;

    let param_set: HashSet<&str> = spec.parameters.iter().map(|p| p.name.as_str()).collect();
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
            let ctx = format!("{}.{}", ec.name, item.name);
            check_poly_vars(&item.expr, &param_set, item.span, &ctx, control)?;
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
