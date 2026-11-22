//! `shigure diagram`・`shigure path`・`shigure transfer` の共通静的検査ヘルパ。

use super::ast_ext::*;
use super::check::{
    CResult, DeclCategory, LiteralDomainRule, check_poly_literals, check_poly_vars,
    resolve_shigure_ref,
};
use super::*;
use crate::law::ast::Span;
use crate::law::check::{Checker, duplicate, reference};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;
use archsig_common::prime::is_prime_controlled;
use num_bigint::BigInt;
use num_traits::Zero;
use std::collections::{BTreeMap, HashMap, HashSet};

pub(super) fn check_scalar_lit<E: InputError>(
    lit: &ShigureScalarLit,
    domain: &ShigureCoeffDomain,
    span: Span,
    control: &Control,
) -> CResult<(), E> {
    match (lit, domain) {
        (ShigureScalarLit::Int(_), ShigureCoeffDomain::Z | ShigureCoeffDomain::Q) => Ok(()),
        (ShigureScalarLit::Int(n), ShigureCoeffDomain::Fp(p)) => {
            if n.to_biguint().is_some_and(|u| &u < p) {
                Ok(())
            } else {
                Err(Box::new(Issue::law(
                    Code::Type,
                    span,
                    format!("integer literal `{n}` in Fp({p}) must satisfy 0 <= value < {p}"),
                ))
                .into())
            }
        }
        (ShigureScalarLit::Rat { den, .. }, ShigureCoeffDomain::Q) => {
            if *den <= BigInt::zero() {
                Err(Box::new(Issue::law(
                    Code::Type,
                    span,
                    "rational denominator must be positive",
                ))
                .into())
            } else {
                Ok(())
            }
        }
        (ShigureScalarLit::Rat { .. }, _) => Err(Box::new(Issue::law(
            Code::Type,
            span,
            "rational literal `rat(n,d)` is only valid in coefficient domain Q",
        ))
        .into()),
        (ShigureScalarLit::Fp { value, modulus }, ShigureCoeffDomain::Fp(expected)) => {
            if !is_prime_controlled::<E>(modulus, control, Checkpoint::LawSemantics)? {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    span,
                    format!("Fp literal modulus `{modulus}` must be prime"),
                ))
                .into());
            }
            if modulus != expected {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    span,
                    "Fp literal modulus does not match declaration coefficient domain",
                ))
                .into());
            }
            if value >= modulus {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    span,
                    format!("Fp literal `{value}` must satisfy 0 <= value < {modulus}"),
                ))
                .into());
            }
            Ok(())
        }
        (ShigureScalarLit::Fp { .. }, _) => Err(Box::new(Issue::law(
            Code::Type,
            span,
            "Fp literal is incompatible with coefficient domain",
        ))
        .into()),
    }
}

pub(super) fn check_state_law_list<E: InputError>(
    raw_laws: &[RawStateLawDecl],
    coeff_domain: &ShigureCoeffDomain,
    dup_context: &str,
    control: &Control,
) -> CResult<Vec<ShigureStateLawDecl>, E> {
    let mut seen = HashSet::new();
    let mut out = Vec::with_capacity(raw_laws.len());
    for l in raw_laws {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !seen.insert(l.name.name.clone()) {
            return duplicate(
                l.name.span,
                format!("duplicate state law `{}` in {dup_context}", l.name.name),
            );
        }
        check_poly_literals(
            &l.expr,
            LiteralDomainRule::Exact(coeff_domain),
            l.span,
            control,
        )?;
        out.push(ShigureStateLawDecl {
            name: l.name.name.clone(),
            kind: l.kind,
            expr: l.expr.clone(),
            span: l.span,
        });
    }
    Ok(out)
}

pub(super) fn check_eval_cond_against_domain_params<E: InputError>(
    ec: &ShigureEvalCondition,
    coeff_domain: &ShigureCoeffDomain,
    param_set: &HashSet<&str>,
    span: Span,
    control: &Control,
) -> CResult<(), E> {
    let compatible = match (coeff_domain, &ec.point_domain) {
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
            span,
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
            LiteralDomainRule::Exact(coeff_domain),
            item.span,
            control,
        )?;
        let ctx = format!("{}.{}", ec.name, item.name);
        check_poly_vars(&item.expr, param_set, item.span, &ctx, control)?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_morphism_body<E: InputError>(
    raw: &RawMorphismBody,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span, usize)>,
    decls: &CheckedShigureDecls,
    edges: &mut Vec<(usize, usize, Span)>,
    morph_src_pres: &ShigurePresentation,
    morph_tgt_pres: &ShigurePresentation,
    params: Option<&HashSet<&str>>,
    span: Span,
    context: &str,
    control: &Control,
) -> CResult<ShigureMorphismBody, E> {
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
            let cmp_name = resolve_shigure_ref(
                qname,
                DeclCategory::Comparison,
                r_idx,
                reading_name,
                checker,
                index,
                edges,
            )?;
            let cmp = &decls.comparisons[&cmp_name];
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

pub(super) struct ScopedMorphismMeta<'a> {
    pub sc_after_phases: Vec<&'a str>,
    pub wt_after_ops: Vec<&'a str>,
    pub is_fixed: bool,
}

impl<'a> ScopedMorphismMeta<'a> {
    pub(super) fn from_body(
        body: &'a ShigureMorphismBody,
        src_pres: &'a ShigurePresentation,
        decls: &'a CheckedShigureDecls,
        is_fixed: bool,
    ) -> Self {
        match body {
            ShigureMorphismBody::Comparison(name) => {
                let cmp = &decls.comparisons[name];
                Self {
                    sc_after_phases: cmp
                        .state_comparisons
                        .iter()
                        .map(|s| s.after_phase.as_str())
                        .collect(),
                    wt_after_ops: cmp
                        .word_translation
                        .iter()
                        .map(|w| w.after_operation.as_str())
                        .collect(),
                    is_fixed,
                }
            }
            ShigureMorphismBody::Identity => Self {
                sc_after_phases: src_pres.phases.iter().map(|p| p.name.as_str()).collect(),
                wt_after_ops: src_pres
                    .operations
                    .iter()
                    .map(|o| o.name.as_str())
                    .collect(),
                is_fixed,
            },
            ShigureMorphismBody::Inline {
                state_comparisons,
                word_translation,
            } => Self {
                sc_after_phases: state_comparisons
                    .iter()
                    .map(|s| s.after_phase.as_str())
                    .collect(),
                wt_after_ops: word_translation
                    .iter()
                    .map(|w| w.after_operation.as_str())
                    .collect(),
                is_fixed,
            },
        }
    }
}

pub(super) fn check_scoped_change_spec_targets<E: InputError>(
    spec: &ShigureChangeSpec,
    pres_map: &BTreeMap<&str, Vec<(&ShigurePresentation, bool)>>,
    morphs: &[ScopedMorphismMeta<'_>],
    label: &str,
    control: &Control,
) -> CResult<(), E> {
    for (target, span) in &spec.fixed {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        match target {
            ShigureFixedTarget::SemanticLaw {
                presentation,
                phase,
                law,
            }
            | ShigureFixedTarget::RepresentationLaw {
                presentation,
                phase,
                law,
            } => {
                let Some(vs) = pres_map.get(presentation.as_str()) else {
                    return reference(
                        *span,
                        format!(
                            "fixed target references presentation `{presentation}` outside {label}"
                        ),
                    );
                };
                if !vs.iter().any(|(p, _)| {
                    p.phases
                        .iter()
                        .find(|ph| ph.name == *phase)
                        .is_some_and(|ph| ph.state_laws.iter().any(|l| l.name == *law))
                }) {
                    return reference(
                        *span,
                        format!("unknown state law `{presentation}.{phase}.{law}` in {label}"),
                    );
                }
            }
            ShigureFixedTarget::OperationExpr {
                presentation,
                operation,
            } => {
                let Some(vs) = pres_map.get(presentation.as_str()) else {
                    return reference(
                        *span,
                        format!(
                            "fixed target references presentation `{presentation}` outside {label}"
                        ),
                    );
                };
                if !vs
                    .iter()
                    .any(|(p, _)| p.operations.iter().any(|o| o.name == *operation))
                {
                    return reference(
                        *span,
                        format!("unknown operation `{presentation}.{operation}` in {label}"),
                    );
                }
            }
            ShigureFixedTarget::ObservationExpr {
                presentation,
                phase,
                observation,
            } => {
                let Some(vs) = pres_map.get(presentation.as_str()) else {
                    return reference(
                        *span,
                        format!(
                            "fixed target references presentation `{presentation}` outside {label}"
                        ),
                    );
                };
                if !vs.iter().any(|(p, _)| {
                    p.observations
                        .iter()
                        .any(|o| o.phase == *phase && o.name == *observation)
                }) {
                    return reference(
                        *span,
                        format!(
                            "unknown observation `{presentation}.{phase}.{observation}` in {label}"
                        ),
                    );
                }
            }
            ShigureFixedTarget::StateComparisonExpr { after_phase } => {
                if !morphs
                    .iter()
                    .any(|m| m.sc_after_phases.contains(&after_phase.as_str()))
                {
                    return reference(
                        *span,
                        format!("fixed state_comparison `{after_phase}` not found in {label}"),
                    );
                }
            }
            ShigureFixedTarget::WordTranslationOp { operation } => {
                if !morphs
                    .iter()
                    .any(|m| m.wt_after_ops.contains(&operation.as_str()))
                {
                    return reference(
                        *span,
                        format!("fixed word_translation `{operation}` not found in {label}"),
                    );
                }
            }
        }
    }

    for (target, span) in &spec.editable {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        match target {
            ShigureEditableTarget::OperationExpr {
                presentation,
                operation,
            } => {
                let Some(vs) = pres_map.get(presentation.as_str()) else {
                    return reference(
                        *span,
                        format!(
                            "editable target references presentation `{presentation}` outside {label}"
                        ),
                    );
                };
                if !vs
                    .iter()
                    .any(|(p, _)| p.operations.iter().any(|o| o.name == *operation))
                {
                    return reference(
                        *span,
                        format!("unknown operation `{presentation}.{operation}` in {label}"),
                    );
                }
                if vs.iter().any(|(_, is_fixed)| *is_fixed) {
                    return Err(Box::new(Issue::law(
                        Code::Type,
                        *span,
                        format!(
                            "editable target `{presentation}.{operation}` cannot belong to a fixed vertex"
                        ),
                    ))
                    .into());
                }
            }
            ShigureEditableTarget::RepresentationLaw {
                presentation,
                phase,
                law,
            } => {
                let Some(vs) = pres_map.get(presentation.as_str()) else {
                    return reference(
                        *span,
                        format!(
                            "editable target references presentation `{presentation}` outside {label}"
                        ),
                    );
                };
                if !vs.iter().any(|(p, _)| {
                    p.phases
                        .iter()
                        .find(|ph| ph.name == *phase)
                        .is_some_and(|ph| ph.state_laws.iter().any(|l| l.name == *law))
                }) {
                    return reference(
                        *span,
                        format!(
                            "unknown representation_law `{presentation}.{phase}.{law}` in {label}"
                        ),
                    );
                }
                if vs.iter().any(|(_, is_fixed)| *is_fixed) {
                    return Err(Box::new(Issue::law(
                        Code::Type,
                        *span,
                        format!(
                            "editable target `{presentation}.{phase}.{law}` cannot belong to a fixed vertex"
                        ),
                    ))
                    .into());
                }
            }
            ShigureEditableTarget::StateComparisonExpr { after_phase } => {
                let any_exists = morphs
                    .iter()
                    .any(|m| m.sc_after_phases.contains(&after_phase.as_str()));
                if !any_exists {
                    return reference(
                        *span,
                        format!("editable state_comparison `{after_phase}` not found in {label}"),
                    );
                }
                let editable_exists = morphs
                    .iter()
                    .any(|m| !m.is_fixed && m.sc_after_phases.contains(&after_phase.as_str()));
                if !editable_exists {
                    return Err(Box::new(Issue::law(
                        Code::Type,
                        *span,
                        format!(
                            "editable state_comparison `{after_phase}` cannot belong only to fixed edges"
                        ),
                    ))
                    .into());
                }
            }
        }
    }
    Ok(())
}
