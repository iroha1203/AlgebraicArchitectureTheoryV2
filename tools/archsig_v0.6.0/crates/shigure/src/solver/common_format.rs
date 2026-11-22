//! Phase 2 復元済み表現・射のパラメータ代入、整形、および独立再評価検算ヘルパ。

use crate::algebra::{
    ExprBindings, GroebnerBasis, MonomialOrder, Poly, Rat, VarOrder, rabinowitsch_solve,
};
use crate::ir::change::{ChangeSpec, EvalCondition, NamedPoly, PointDomain};
use crate::ir::morphism::StateMorphism;
use crate::ir::presentation::{
    CoordValue, ObservationDecl, OperationDecl, PhaseDecl, Presentation, StateComparison, StateLaw,
    TranslatedStep, TranslatedWord, WordTranslation,
};
use crate::ir::provenance::SourceRef;
use crate::ir::result::{ReevalCheck, SilenceReason};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::solver::common_solve::{ParamWitness, decide_z_quotient_unit_safe};
use crate::solver::preservation::{
    PreservationObligation, compute_preservation_locus_q, extract_closed_residuals_fp,
    is_stratum_covered_by_union, map_algebra_silence, substitute_poly_expr,
};
use num_traits::{One, Signed, Zero};
use std::collections::{BTreeMap, BTreeSet};

/// パラメータ置換 `param_subst` を `Presentation` に適用する。
pub(crate) fn substitute_presentation(
    pres: &Presentation,
    param_subst: &BTreeMap<String, PolyExpr>,
) -> Presentation {
    let empty = BTreeMap::new();
    let phases = pres
        .phases
        .iter()
        .map(|ph| PhaseDecl {
            name: ph.name.clone(),
            coords: ph.coords.clone(),
            state_laws: ph
                .state_laws
                .iter()
                .map(|l| StateLaw {
                    name: l.name.clone(),
                    kind: l.kind,
                    polynomial: substitute_poly_expr(&l.polynomial, &empty, &empty, param_subst),
                    provenance: l.provenance.clone(),
                })
                .collect(),
            provenance: ph.provenance.clone(),
        })
        .collect();
    let operations = pres
        .operations
        .iter()
        .map(|op| OperationDecl {
            name: op.name.clone(),
            source_phase: op.source_phase.clone(),
            target_phase: op.target_phase.clone(),
            args: op.args.clone(),
            domain_laws: op
                .domain_laws
                .iter()
                .map(|l| StateLaw {
                    name: l.name.clone(),
                    kind: l.kind,
                    polynomial: substitute_poly_expr(&l.polynomial, &empty, &empty, param_subst),
                    provenance: l.provenance.clone(),
                })
                .collect(),
            updates: op
                .updates
                .iter()
                .map(|(k, v)| {
                    (
                        k.clone(),
                        substitute_poly_expr(v, &empty, &empty, param_subst),
                    )
                })
                .collect(),
            provenance: op.provenance.clone(),
        })
        .collect();
    let observations = pres
        .observations
        .iter()
        .map(|obs| ObservationDecl {
            name: obs.name.clone(),
            phase: obs.phase.clone(),
            components: obs
                .components
                .iter()
                .map(|e| substitute_poly_expr(e, &empty, &empty, param_subst))
                .collect(),
            provenance: obs.provenance.clone(),
        })
        .collect();
    Presentation {
        name: pres.name.clone(),
        coeff_domain: pres.coeff_domain.clone(),
        sorts: pres.sorts.clone(),
        phases,
        operations,
        observations,
        provenance: pres.provenance.clone(),
    }
}

/// パラメータ置換 `param_subst` を `StateMorphism` に適用する。
pub(crate) fn substitute_state_morphism(
    m: &StateMorphism,
    param_subst: &BTreeMap<String, PolyExpr>,
) -> StateMorphism {
    let empty = BTreeMap::new();
    StateMorphism {
        source: m.source.clone(),
        target: m.target.clone(),
        state_comparisons: m
            .state_comparisons
            .iter()
            .map(|sc| StateComparison {
                after_phase: sc.after_phase.clone(),
                before_phase: sc.before_phase.clone(),
                map: sc
                    .map
                    .iter()
                    .map(|(k, v)| {
                        (
                            k.clone(),
                            substitute_poly_expr(v, &empty, &empty, param_subst),
                        )
                    })
                    .collect(),
                provenance: sc.provenance.clone(),
            })
            .collect(),
        word_translation: WordTranslation {
            entries: m
                .word_translation
                .entries
                .iter()
                .map(|tw| TranslatedWord {
                    after_operation: tw.after_operation.clone(),
                    steps: tw
                        .steps
                        .iter()
                        .map(|st| TranslatedStep {
                            before_operation: st.before_operation.clone(),
                            arg_exprs: st
                                .arg_exprs
                                .iter()
                                .map(|e| substitute_poly_expr(e, &empty, &empty, param_subst))
                                .collect(),
                        })
                        .collect(),
                    provenance: tw.provenance.clone(),
                })
                .collect(),
        },
        provenance: m.provenance.clone(),
    }
}

/// パラメータ置換 `param_subst` を `EvalCondition` に適用する。
pub(crate) fn substitute_eval_condition(
    cond: &EvalCondition,
    param_subst: &BTreeMap<String, PolyExpr>,
) -> EvalCondition {
    let empty = BTreeMap::new();
    let sub_list = |items: &[NamedPoly]| -> Vec<NamedPoly> {
        items
            .iter()
            .map(|np| NamedPoly {
                name: np.name.clone(),
                expr: substitute_poly_expr(&np.expr, &empty, &empty, param_subst),
                provenance: np.provenance.clone(),
            })
            .collect()
    };
    EvalCondition {
        name: cond.name.clone(),
        evaluations: sub_list(&cond.evaluations),
        equations: sub_list(&cond.equations),
        invertibles: sub_list(&cond.invertibles),
        point_domain: cond.point_domain.clone(),
        provenance: cond.provenance.clone(),
    }
}

/// 整形済みの `(写像/演算マップ, Law/翻訳リストマップ)` 対。
pub(crate) type FormattedMapPair = (
    BTreeMap<String, BTreeMap<String, String>>,
    BTreeMap<String, Vec<String>>,
);

/// 復元済み `Presentation` の操作更新式・状態 Law を文字列表現へ整形する。
pub(crate) fn format_presentation(
    pres: &Presentation,
    free_params: &[String],
) -> Result<FormattedMapPair, SilenceReason> {
    let empty = BTreeMap::new();
    let phases: BTreeMap<&str, &PhaseDecl> =
        pres.phases.iter().map(|p| (p.name.as_str(), p)).collect();
    let mut operations = BTreeMap::new();
    for op in &pres.operations {
        let src = phases[op.source_phase.as_str()];
        let (sv, obs) = symbolic_and_observed(src);
        let av: Vec<String> = op.args.iter().map(|(a, _)| a.clone()).collect();
        let (order, bind) =
            ExprBindings::from_slices(&sv, &av, free_params).map_err(map_algebra_silence)?;
        let mut updates = BTreeMap::new();
        for (coord, expr) in &op.updates {
            let sub = substitute_poly_expr(expr, &obs, &empty, &empty);
            updates.insert(
                coord.clone(),
                fmt_poly_expr(&sub, &bind, &order, &pres.coeff_domain)?,
            );
        }
        operations.insert(op.name.clone(), updates);
    }
    let mut state_laws = BTreeMap::new();
    for ph in &pres.phases {
        let (sv, obs) = symbolic_and_observed(ph);
        let (order, bind) =
            ExprBindings::from_slices(&sv, &[], free_params).map_err(map_algebra_silence)?;
        let mut laws = Vec::new();
        for l in &ph.state_laws {
            let sub = substitute_poly_expr(&l.polynomial, &obs, &empty, &empty);
            laws.push(fmt_poly_expr(&sub, &bind, &order, &pres.coeff_domain)?);
        }
        state_laws.insert(ph.name.clone(), laws);
    }
    Ok((operations, state_laws))
}

/// 復元済み `StateMorphism` の状態比較射と語翻訳を文字列表現へ整形する。
pub(crate) fn format_state_morphism(
    m: &StateMorphism,
    src_pres: &Presentation,
    free_params: &[String],
) -> Result<FormattedMapPair, SilenceReason> {
    let empty = BTreeMap::new();
    let phases: BTreeMap<&str, &PhaseDecl> = src_pres
        .phases
        .iter()
        .map(|p| (p.name.as_str(), p))
        .collect();
    let ops: BTreeMap<&str, &OperationDecl> = src_pres
        .operations
        .iter()
        .map(|o| (o.name.as_str(), o))
        .collect();

    let mut state_comparisons = BTreeMap::new();
    for sc in &m.state_comparisons {
        let ph = phases[sc.after_phase.as_str()];
        let (sv, obs) = symbolic_and_observed(ph);
        let (order, bind) =
            ExprBindings::from_slices(&sv, &[], free_params).map_err(map_algebra_silence)?;
        let mut map = BTreeMap::new();
        for (coord, expr) in &sc.map {
            let sub = substitute_poly_expr(expr, &obs, &empty, &empty);
            map.insert(
                coord.clone(),
                fmt_poly_expr(&sub, &bind, &order, &src_pres.coeff_domain)?,
            );
        }
        state_comparisons.insert(sc.after_phase.clone(), map);
    }

    let mut word_translation = BTreeMap::new();
    for tw in &m.word_translation.entries {
        let op = ops[tw.after_operation.as_str()];
        let src = phases[op.source_phase.as_str()];
        let (sv, obs) = symbolic_and_observed(src);
        let av: Vec<String> = op.args.iter().map(|(a, _)| a.clone()).collect();
        let (order, bind) =
            ExprBindings::from_slices(&sv, &av, free_params).map_err(map_algebra_silence)?;
        let mut steps = Vec::new();
        for st in &tw.steps {
            let mut arg_strs = Vec::new();
            for ae in &st.arg_exprs {
                let sub = substitute_poly_expr(ae, &obs, &empty, &empty);
                arg_strs.push(fmt_poly_expr(&sub, &bind, &order, &src_pres.coeff_domain)?);
            }
            if arg_strs.is_empty() {
                steps.push(st.before_operation.clone());
            } else {
                steps.push(format!("{}({})", st.before_operation, arg_strs.join(", ")));
            }
        }
        word_translation.insert(tw.after_operation.clone(), steps);
    }
    Ok((state_comparisons, word_translation))
}

pub(crate) fn fmt_poly_expr(
    expr: &PolyExpr,
    bind: &ExprBindings,
    order: &VarOrder,
    domain: &CoeffDomain,
) -> Result<String, SilenceReason> {
    match domain {
        CoeffDomain::Q => Ok(Poly::from_expr_q(expr, bind)
            .map_err(map_algebra_silence)?
            .display(order, MonomialOrder::Grevlex)),
        CoeffDomain::Z => Ok(Poly::from_expr_z(expr, bind)
            .map_err(map_algebra_silence)?
            .display(order, MonomialOrder::Grevlex)),
        CoeffDomain::Fp(m) => Ok(Poly::from_expr_fp(expr, bind, m)
            .map_err(map_algebra_silence)?
            .display(order, MonomialOrder::Grevlex)),
    }
}

pub(crate) fn symbolic_and_observed(
    phase: &PhaseDecl,
) -> (Vec<String>, BTreeMap<String, PolyExpr>) {
    let mut symbolic = Vec::new();
    let mut observed = BTreeMap::new();
    for c in &phase.coords {
        match &c.value {
            CoordValue::Symbolic => symbolic.push(c.name.clone()),
            CoordValue::Observed(lit) => {
                observed.insert(c.name.clone(), PolyExpr::Const(lit.clone()));
            }
            CoordValue::Missing => {}
        }
    }
    (symbolic, observed)
}

fn fail_reeval(detail: impl Into<String>) -> ReevalCheck {
    ReevalCheck {
        checked: true,
        matched: false,
        detail: detail.into(),
    }
}

/// 復元済み表現から構成した保存義務および制約式列が、自由パラメータと開条件のもとで
/// 厳密に含意されるかを独立に再評価検算する。
pub(crate) fn reeval_obligations_and_constraints(
    obligations: &[PreservationObligation],
    extra_eqs: &[PolyExpr],
    eval_conds: &[&EvalCondition],
    witness: &ParamWitness,
    coeff_domain: &CoeffDomain,
    point_domain: &PointDomain,
    context_label: &str,
) -> Result<ReevalCheck, SilenceReason> {
    match witness {
        ParamWitness::QSubst { subst } => reeval_q_subst(
            obligations,
            extra_eqs,
            eval_conds,
            subst,
            point_domain,
            context_label,
        ),
        ParamWitness::QPoint { .. } => {
            reeval_zero_param_q(obligations, extra_eqs, eval_conds, false, context_label)
        }
        ParamWitness::ZPoint { .. } => match coeff_domain {
            CoeffDomain::Q => {
                reeval_zero_param_q(obligations, extra_eqs, eval_conds, true, context_label)
            }
            CoeffDomain::Z => {
                reeval_zero_param_z(obligations, extra_eqs, eval_conds, context_label)
            }
            CoeffDomain::Fp(_) => Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "reeval_domain_match".to_owned(),
                detail: "Z witness does not match Fp coefficient domain".to_owned(),
            }),
        },
        ParamWitness::FpPoint { modulus, .. } => {
            let empty_order = VarOrder::new(vec![]).map_err(map_algebra_silence)?;
            let empty_bind = ExprBindings::params_only(&empty_order);
            let Some(residuals) = extract_closed_residuals_fp(obligations, &[], modulus)? else {
                return Err(SilenceReason::QuotientIdealOutOfScope {
                    detail: "quotient state-law re-evaluation over Fp is out of scope".to_owned(),
                });
            };
            if residuals.iter().any(|p| !p.is_zero()) {
                return Ok(fail_reeval(format!(
                    "restored {context_label} has nonzero Fp preservation residual"
                )));
            }
            for ex in extra_eqs {
                let p =
                    Poly::from_expr_fp(ex, &empty_bind, modulus).map_err(map_algebra_silence)?;
                if !p.is_zero() {
                    return Ok(fail_reeval(format!(
                        "restored {context_label} violated extra equality constraint over Fp"
                    )));
                }
            }
            for cond in eval_conds {
                for eq in &cond.equations {
                    let p = Poly::from_expr_fp(&eq.expr, &empty_bind, modulus)
                        .map_err(map_algebra_silence)?;
                    if !p.is_zero() {
                        return Ok(fail_reeval(format!(
                            "eval equation `{}` did not vanish over Fp",
                            eq.name
                        )));
                    }
                }
                for inv in &cond.invertibles {
                    let p = Poly::from_expr_fp(&inv.expr, &empty_bind, modulus)
                        .map_err(map_algebra_silence)?;
                    if p.is_zero() {
                        return Ok(fail_reeval(format!(
                            "eval invertible `{}` vanished over Fp",
                            inv.name
                        )));
                    }
                }
            }
            Ok(ReevalCheck {
                checked: true,
                matched: true,
                detail: format!(
                    "verified all {} obligations on restored Fp({modulus}) {context_label}",
                    obligations.len()
                ),
            })
        }
    }
}

fn reeval_q_subst(
    obligations: &[PreservationObligation],
    extra_eqs: &[PolyExpr],
    eval_conds: &[&EvalCondition],
    subst: &crate::solver::restore::ExtractedSubstitutionQ,
    point_domain: &PointDomain,
    context_label: &str,
) -> Result<ReevalCheck, SilenceReason> {
    let free_order =
        VarOrder::new(subst.unassigned_parameters.clone()).map_err(map_algebra_silence)?;
    let free_bind = ExprBindings::params_only(&free_order);
    let locus = compute_preservation_locus_q(obligations, &free_order)?;

    let mut eval_eqs = subst.remaining_nonlinear.clone();
    let mut eval_invs = Vec::new();
    for ex in extra_eqs {
        let p = Poly::from_expr_q(ex, &free_bind).map_err(map_algebra_silence)?;
        if !p.is_zero() {
            eval_eqs.push(p);
        }
    }
    for cond in eval_conds {
        for eq in &cond.equations {
            let p = Poly::from_expr_q(&eq.expr, &free_bind).map_err(map_algebra_silence)?;
            if !p.is_zero() {
                eval_eqs.push(p);
            }
        }
        for inv in &cond.invertibles {
            let p = Poly::from_expr_q(&inv.expr, &free_bind).map_err(map_algebra_silence)?;
            if !eval_invs.contains(&p) {
                eval_invs.push(p);
            }
        }
    }

    let target_rab =
        rabinowitsch_solve(&eval_eqs, &eval_invs, &free_order).map_err(map_algebra_silence)?;
    if target_rab.is_empty_over_closure || locus.strata.is_empty() {
        return Ok(fail_reeval(format!(
            "restored {context_label} violates obligations or evaluation conditions"
        )));
    }

    if *point_domain == PointDomain::UniversalRing {
        if !locus.is_zariski_closed {
            return Ok(fail_reeval(format!(
                "restored {context_label} locus is not Zariski-closed for UniversalRing"
            )));
        }
        let sat_gb = GroebnerBasis::compute(
            &target_rab.parameter_equations,
            free_order.clone(),
            MonomialOrder::Grevlex,
        )
        .map_err(map_algebra_silence)?;
        for res_poly in &locus.closure_ideal {
            let nf = sat_gb.normal_form(res_poly).map_err(map_algebra_silence)?;
            if !nf.is_zero() {
                return Ok(fail_reeval(format!(
                    "restored {context_label} residual `{}` did not vanish modulo constraints",
                    res_poly.display(&free_order, MonomialOrder::Grevlex)
                )));
            }
        }
    } else if !is_stratum_covered_by_union(
        &target_rab.parameter_equations,
        &eval_invs,
        &locus.strata,
        &free_order,
    )? {
        return Ok(fail_reeval(format!(
            "restored {context_label} constraint locus is not covered by preservation locus"
        )));
    }

    Ok(ReevalCheck {
        checked: true,
        matched: true,
        detail: format!(
            "verified all {} obligations on restored {context_label}",
            obligations.len()
        ),
    })
}

fn reeval_zero_param_q(
    obligations: &[PreservationObligation],
    extra_eqs: &[PolyExpr],
    eval_conds: &[&EvalCondition],
    require_z_unit_invs: bool,
    context_label: &str,
) -> Result<ReevalCheck, SilenceReason> {
    let empty_order = VarOrder::new(vec![]).map_err(map_algebra_silence)?;
    let empty_bind = ExprBindings::params_only(&empty_order);
    let locus = compute_preservation_locus_q(obligations, &empty_order)?;
    if locus.strata.is_empty() {
        return Ok(fail_reeval(format!(
            "restored {context_label} failed independent preservation check"
        )));
    }
    for ex in extra_eqs {
        let p = Poly::from_expr_q(ex, &empty_bind).map_err(map_algebra_silence)?;
        if !p.is_zero() {
            return Ok(fail_reeval(format!(
                "restored {context_label} violated extra equality constraint"
            )));
        }
    }
    for cond in eval_conds {
        for eq in &cond.equations {
            let p = Poly::from_expr_q(&eq.expr, &empty_bind).map_err(map_algebra_silence)?;
            if !p.is_zero() {
                return Ok(fail_reeval(format!(
                    "eval equation `{}` did not vanish",
                    eq.name
                )));
            }
        }
        for inv in &cond.invertibles {
            let p = Poly::from_expr_q(&inv.expr, &empty_bind).map_err(map_algebra_silence)?;
            let val = p.constant_value();
            let valid = if require_z_unit_invs {
                val.den().is_one() && val.num().abs().is_one()
            } else {
                !p.is_zero()
            };
            if !valid {
                return Ok(fail_reeval(format!(
                    "eval invertible `{}` does not hold at restored point",
                    inv.name
                )));
            }
        }
    }
    Ok(ReevalCheck {
        checked: true,
        matched: true,
        detail: format!(
            "verified all {} obligations on restored {context_label}",
            obligations.len()
        ),
    })
}

fn reeval_zero_param_z(
    obligations: &[PreservationObligation],
    extra_eqs: &[PolyExpr],
    eval_conds: &[&EvalCondition],
    context_label: &str,
) -> Result<ReevalCheck, SilenceReason> {
    let empty_order = VarOrder::new(vec![]).map_err(map_algebra_silence)?;
    let empty_bind = ExprBindings::params_only(&empty_order);
    for ob in obligations {
        if ob.source_laws.is_empty() {
            let (_, ob_bind) = ExprBindings::from_slices(&ob.state_vars, &ob.arg_vars, &[])
                .map_err(map_algebra_silence)?;
            let p = Poly::from_expr_z(&ob.target, &ob_bind).map_err(map_algebra_silence)?;
            if !p.is_zero() {
                return Ok(fail_reeval(format!(
                    "restored {context_label} has nonzero preservation residual over Z"
                )));
            }
        } else {
            match decide_z_quotient_unit_safe(ob, &empty_order)? {
                Some(true) => {}
                Some(false) => {
                    return Ok(fail_reeval(format!(
                        "restored {context_label} failed Z quotient state-law check"
                    )));
                }
                None => {
                    return Err(SilenceReason::QuotientIdealOutOfScope {
                        detail: "Z quotient re-evaluation outside unit-pivot scope".to_owned(),
                    });
                }
            }
        }
    }
    for ex in extra_eqs {
        let p = Poly::from_expr_z(ex, &empty_bind).map_err(map_algebra_silence)?;
        if !p.is_zero() {
            return Ok(fail_reeval(format!(
                "restored {context_label} violated extra equality constraint over Z"
            )));
        }
    }
    for cond in eval_conds {
        for eq in &cond.equations {
            let p = Poly::from_expr_z(&eq.expr, &empty_bind).map_err(map_algebra_silence)?;
            if !p.is_zero() {
                return Ok(fail_reeval(format!(
                    "eval equation `{}` did not vanish over Z",
                    eq.name
                )));
            }
        }
        for inv in &cond.invertibles {
            let p = Poly::from_expr_z(&inv.expr, &empty_bind).map_err(map_algebra_silence)?;
            let val = p.constant_value();
            if val.is_zero() || !val.abs().is_one() {
                return Ok(fail_reeval(format!(
                    "eval invertible `{}` is not a unit in Z",
                    inv.name
                )));
            }
        }
    }
    Ok(ReevalCheck {
        checked: true,
        matched: true,
        detail: format!(
            "verified all {} obligations on restored Z {context_label}",
            obligations.len()
        ),
    })
}

pub(crate) fn collect_presentation_origins(pres: &Presentation, set: &mut BTreeSet<SourceRef>) {
    for o in &pres.provenance.origins {
        set.insert(o.clone());
    }
    for s in &pres.sorts {
        if let Some(o) = &s.provenance {
            set.insert(o.clone());
        }
    }
    for p in &pres.phases {
        if let Some(o) = &p.provenance {
            set.insert(o.clone());
        }
        for c in &p.coords {
            if let Some(o) = &c.provenance {
                set.insert(o.clone());
            }
        }
        for l in &p.state_laws {
            if let Some(o) = &l.provenance {
                set.insert(o.clone());
            }
        }
    }
    for op in &pres.operations {
        if let Some(o) = &op.provenance {
            set.insert(o.clone());
        }
        for dl in &op.domain_laws {
            if let Some(o) = &dl.provenance {
                set.insert(o.clone());
            }
        }
    }
    for obs in &pres.observations {
        if let Some(o) = &obs.provenance {
            set.insert(o.clone());
        }
    }
}

pub(crate) fn collect_morphism_origins(m: &StateMorphism, set: &mut BTreeSet<SourceRef>) {
    if let Some(o) = &m.provenance {
        set.insert(o.clone());
    }
    for sc in &m.state_comparisons {
        if let Some(o) = &sc.provenance {
            set.insert(o.clone());
        }
    }
    for tw in &m.word_translation.entries {
        if let Some(o) = &tw.provenance {
            set.insert(o.clone());
        }
    }
}

pub(crate) fn collect_change_and_eval_origins(
    cs: &ChangeSpec,
    eval_conds: &[&EvalCondition],
    set: &mut BTreeSet<SourceRef>,
) {
    for o in &cs.provenance.origins {
        set.insert(o.clone());
    }
    for p in &cs.parameters {
        if let Some(o) = &p.provenance {
            set.insert(o.clone());
        }
    }
    for cond in eval_conds {
        for o in &cond.provenance.origins {
            set.insert(o.clone());
        }
        for item in cond
            .evaluations
            .iter()
            .chain(&cond.equations)
            .chain(&cond.invertibles)
        {
            if let Some(o) = &item.provenance {
                set.insert(o.clone());
            }
        }
    }
}

/// パラメータ多項式 `Poly<Rat>` を対応する `PolyExpr`（`ParamVar`）へ変換する。
pub(crate) fn poly_q_to_expr(poly: &Poly<Rat>, vars: &VarOrder) -> PolyExpr {
    if poly.is_zero() {
        return PolyExpr::int(0);
    }
    let mut acc: Option<PolyExpr> = None;
    for (mono, coeff) in poly.terms() {
        let mut term = if coeff.den().is_one() {
            PolyExpr::Const(ScalarLit::Z(coeff.num().clone()))
        } else {
            PolyExpr::Const(ScalarLit::Q {
                num: coeff.num().clone(),
                den: coeff.den().clone(),
            })
        };
        for (idx, &exp) in mono.exps().iter().enumerate() {
            if exp > 0 {
                let v = PolyExpr::ParamVar(vars.vars()[idx].clone());
                let fac = if exp == 1 { v } else { PolyExpr::pow(v, exp) };
                term = PolyExpr::prod(term, fac);
            }
        }
        acc = Some(match acc {
            None => term,
            Some(prev) => PolyExpr::sum(prev, term),
        });
    }
    acc.unwrap_or_else(|| PolyExpr::int(0))
}
