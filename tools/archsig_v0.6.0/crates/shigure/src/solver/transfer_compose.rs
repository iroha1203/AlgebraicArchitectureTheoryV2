//! 状態移送の義務収集・段合成・fiber product 定義域分類・復元整形（G-140 G1・G3）。

use crate::algebra::{
    ExprBindings, GroebnerBasis, MonomialOrder, Poly, Rat, VarOrder, rabinowitsch_solve,
};
use crate::ir::change::{EvalCondition, PointDomain};
use crate::ir::morphism::{StateMorphism, compose_state_order};
use crate::ir::presentation::{ComparisonPair, CoordValue, PhaseDecl, StateLaw};
use crate::ir::result::SilenceReason;
use crate::ir::result_ext::{DomainRelation, TransferStepDiagnostic};
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::ir::transfer::TransferStepSpec;
use crate::solver::common_format::{
    fmt_poly_expr, format_state_morphism, reeval_obligations_and_constraints,
    substitute_presentation, substitute_state_morphism,
};
use crate::solver::common_morph::compare_morphisms;
use crate::solver::common_solve::{
    ParamWitness, collect_eval_and_extra, decide_fp_quotient_exact, decide_z_quotient_unit_safe,
};
use crate::solver::common_solve_q::{IdealNonemptyCtx, is_ideal_nonempty};
use crate::solver::context::display_polys;
use crate::solver::preservation::{
    PreservationObligation, build_preservation_obligations, map_algebra_silence,
    substitute_poly_expr,
};
use crate::solver::transfer::step_domain_env;
use crate::solver::transfer_words::eval_poly_q_or_format;
use std::collections::BTreeMap;

fn collect_single_step_lift_obligations(
    step: &TransferStepSpec,
    sv: &[String],
    obs: &BTreeMap<String, PolyExpr>,
    src_laws: &[PolyExpr],
    tgt_ph: &PhaseDecl,
) -> (Vec<PreservationObligation>, Vec<PreservationObligation>) {
    let empty = BTreeMap::new();
    let lift_sub: BTreeMap<String, PolyExpr> = step
        .lift_map
        .iter()
        .map(|(k, v)| (k.clone(), substitute_poly_expr(v, obs, &empty, &empty)))
        .collect();

    let mut tgt_law_obs = Vec::new();
    for dc in &tgt_ph.coords {
        if let CoordValue::Observed(lit) = &dc.value
            && let Some(expr) = lift_sub.get(&dc.name)
        {
            tgt_law_obs.push(PreservationObligation {
                state_vars: sv.to_vec(),
                arg_vars: vec![],
                source_laws: src_laws.to_vec(),
                target: PolyExpr::diff(expr.clone(), PolyExpr::Const(lit.clone())),
            });
        }
    }
    for tl in &tgt_ph.state_laws {
        tgt_law_obs.push(PreservationObligation {
            state_vars: sv.to_vec(),
            arg_vars: vec![],
            source_laws: src_laws.to_vec(),
            target: substitute_poly_expr(&tl.polynomial, &lift_sub, &empty, &empty),
        });
    }

    let sc = step
        .comparison
        .state_comparisons
        .iter()
        .find(|s| s.after_phase == step.target_phase)
        .expect("checked sc");
    let src_ph = step
        .comparison
        .before
        .phase(&step.source_phase)
        .expect("checked source_phase");
    let mut lift_id_obs = Vec::new();
    for c in &src_ph.coords {
        if let Some(h_expr) = sc.map.get(&c.name) {
            let h_of_m = substitute_poly_expr(h_expr, &lift_sub, &empty, &empty);
            let iota_expr = match &c.value {
                CoordValue::Observed(lit) => PolyExpr::Const(lit.clone()),
                CoordValue::Symbolic | CoordValue::Missing => PolyExpr::StateVar(c.name.clone()),
            };
            lift_id_obs.push(PreservationObligation {
                state_vars: sv.to_vec(),
                arg_vars: vec![],
                source_laws: src_laws.to_vec(),
                target: PolyExpr::diff(h_of_m, iota_expr),
            });
        }
    }
    (tgt_law_obs, lift_id_obs)
}

pub(crate) fn collect_transfer_obligations(
    steps: &[TransferStepSpec],
    param_vars: &VarOrder,
    coeff_domain: &CoeffDomain,
) -> Result<(Vec<PreservationObligation>, Vec<TransferStepDiagnostic>), SilenceReason> {
    let mut all_obs = Vec::new();
    let mut diags = Vec::with_capacity(steps.len());
    for step in steps {
        all_obs.extend(build_preservation_obligations(&step.comparison)?);
        let (sv, obs, src_laws) = step_domain_env(step);
        let tgt_ph = step
            .comparison
            .after
            .phase(&step.target_phase)
            .expect("checked target_phase");
        let (tgt_obs, id_obs) =
            collect_single_step_lift_obligations(step, &sv, &obs, &src_laws, tgt_ph);
        let mut tgt_res = Vec::new();
        for o in &tgt_obs {
            let disp = eval_poly_q_or_format(
                &o.target,
                &o.source_laws,
                &o.state_vars,
                &o.arg_vars,
                param_vars,
                coeff_domain,
            )?;
            if disp != "0" {
                tgt_res.push(disp);
            }
        }
        let mut id_res = Vec::new();
        for o in &id_obs {
            let disp = eval_poly_q_or_format(
                &o.target,
                &o.source_laws,
                &o.state_vars,
                &o.arg_vars,
                param_vars,
                coeff_domain,
            )?;
            if disp != "0" {
                id_res.push(disp);
            }
        }
        all_obs.extend(tgt_obs);
        all_obs.extend(id_obs);
        diags.push(TransferStepDiagnostic {
            step_name: step.name.clone(),
            source_phase: step.source_phase.clone(),
            target_phase: step.target_phase.clone(),
            target_law_residuals: tgt_res,
            lift_residuals: id_res,
        });
    }
    Ok((all_obs, diags))
}

pub(crate) fn substitute_transfer_steps(
    steps: &[TransferStepSpec],
    param_subst: &BTreeMap<String, PolyExpr>,
) -> Vec<TransferStepSpec> {
    let empty = BTreeMap::new();
    steps
        .iter()
        .map(|s| {
            let morph = substitute_state_morphism(
                &StateMorphism::from_comparison_pair(&s.comparison),
                param_subst,
            );
            let before = substitute_presentation(&s.comparison.before, param_subst);
            let after = substitute_presentation(&s.comparison.after, param_subst);
            TransferStepSpec {
                name: s.name.clone(),
                comparison: ComparisonPair {
                    before,
                    after,
                    state_comparisons: morph.state_comparisons,
                    word_translation: morph.word_translation,
                },
                source_phase: s.source_phase.clone(),
                domain_laws: s
                    .domain_laws
                    .iter()
                    .map(|l| StateLaw {
                        name: l.name.clone(),
                        kind: l.kind,
                        polynomial: substitute_poly_expr(
                            &l.polynomial,
                            &empty,
                            &empty,
                            param_subst,
                        ),
                        provenance: l.provenance.clone(),
                    })
                    .collect(),
                target_phase: s.target_phase.clone(),
                lift_map: s
                    .lift_map
                    .iter()
                    .map(|(k, v)| {
                        (
                            k.clone(),
                            substitute_poly_expr(v, &empty, &empty, param_subst),
                        )
                    })
                    .collect(),
                provenance: s.provenance.clone(),
            }
        })
        .collect()
}

pub(crate) struct ComposedTransferData {
    pub composed_h: StateMorphism,
    pub step_lifts: Vec<(String, BTreeMap<String, PolyExpr>)>,
    pub composed_lift: BTreeMap<String, PolyExpr>,
    pub domain_relation: DomainRelation,
    pub d0k_laws: Vec<PolyExpr>,
    pub d0k_display: Vec<String>,
}

pub(crate) fn compose_and_classify_transfer(
    steps: &[TransferStepSpec],
    free_vars: &VarOrder,
    witness: &ParamWitness,
    eval_conds: &[&EvalCondition],
    coeff_domain: &CoeffDomain,
    point_domain: &PointDomain,
) -> Result<ComposedTransferData, SilenceReason> {
    let empty = BTreeMap::new();
    let step_h_morphs: Vec<StateMorphism> = steps
        .iter()
        .map(|s| StateMorphism::from_comparison_pair(&s.comparison))
        .collect();
    let mut comp_h = step_h_morphs[0].clone();
    for (j, next_h) in step_h_morphs.iter().enumerate().skip(1) {
        comp_h = compose_state_order(
            &comp_h,
            next_h,
            &steps[j].comparison.after,
            &steps[j].comparison.before,
        )
        .map_err(|e| SilenceReason::ApplicabilityConditionNotMet {
            condition: "transfer_h_composition".to_owned(),
            detail: e.to_string(),
        })?;
    }
    if steps.len() >= 3 {
        let mut right_h = step_h_morphs.last().expect("last").clone();
        for j in (1..steps.len() - 1).rev() {
            right_h = compose_state_order(
                &step_h_morphs[j],
                &right_h,
                &steps.last().expect("last").comparison.after,
                &steps[j].comparison.after,
            )
            .map_err(|e| SilenceReason::ApplicabilityConditionNotMet {
                condition: "transfer_h_associativity".to_owned(),
                detail: e.to_string(),
            })?;
        }
        let alt_h = compose_state_order(
            &step_h_morphs[0],
            &right_h,
            &steps.last().expect("last").comparison.after,
            &steps[0].comparison.after,
        )
        .map_err(|e| SilenceReason::ApplicabilityConditionNotMet {
            condition: "transfer_h_associativity".to_owned(),
            detail: e.to_string(),
        })?;
        let (a_obs, _, a_mm) = compare_morphisms(
            &comp_h,
            &alt_h,
            &steps.last().expect("last").comparison.after,
            free_vars,
            coeff_domain,
        )?;
        if a_mm.is_some()
            || !reeval_obligations_and_constraints(
                &a_obs,
                &[],
                eval_conds,
                witness,
                coeff_domain,
                point_domain,
                "transfer_h_assoc",
            )?
            .matched
        {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "transfer_h_associativity".to_owned(),
                detail: "3-step transfer morphism composition violated associativity".to_owned(),
            });
        }
    }

    let (d0_sv, d0_obs, d0_laws) = step_domain_env(&steps[0]);
    let mut step_lifts_sub = Vec::with_capacity(steps.len());
    let first_lift: BTreeMap<String, PolyExpr> = steps[0]
        .lift_map
        .iter()
        .map(|(k, v)| (k.clone(), substitute_poly_expr(v, &d0_obs, &empty, &empty)))
        .collect();
    step_lifts_sub.push((steps[0].name.clone(), first_lift.clone()));

    let mut comp_lift = first_lift;
    let mut extra_pb_laws = Vec::new();
    for s in steps.iter().skip(1) {
        let (_, xj_obs, _) = step_domain_env(s);
        let s_lift: BTreeMap<String, PolyExpr> = s
            .lift_map
            .iter()
            .map(|(k, v)| (k.clone(), substitute_poly_expr(v, &xj_obs, &empty, &empty)))
            .collect();
        step_lifts_sub.push((s.name.clone(), s_lift));

        let xj_ph = s
            .comparison
            .before
            .phase(&s.source_phase)
            .expect("source_phase");
        for c in &xj_ph.coords {
            if let CoordValue::Observed(lit) = &c.value
                && let Some(expr) = comp_lift.get(&c.name)
            {
                extra_pb_laws.push(PolyExpr::diff(expr.clone(), PolyExpr::Const(lit.clone())));
            }
        }
        for dl in &s.domain_laws {
            extra_pb_laws.push(substitute_poly_expr(
                &dl.polynomial,
                &comp_lift,
                &empty,
                &empty,
            ));
        }
        comp_lift = s
            .lift_map
            .iter()
            .map(|(k, v)| {
                (
                    k.clone(),
                    substitute_poly_expr(v, &comp_lift, &empty, &empty),
                )
            })
            .collect();
    }

    let mut d0k_laws = d0_laws.clone();
    d0k_laws.extend(extra_pb_laws.iter().cloned());

    let (relation, disp) = classify_domain_relation(
        &d0_sv,
        &d0_laws,
        &extra_pb_laws,
        &d0k_laws,
        free_vars,
        witness,
        eval_conds,
        coeff_domain,
        point_domain,
    )?;

    Ok(ComposedTransferData {
        composed_h: comp_h,
        step_lifts: step_lifts_sub,
        composed_lift: comp_lift,
        domain_relation: relation,
        d0k_laws,
        d0k_display: disp,
    })
}

#[allow(clippy::too_many_arguments)]
fn classify_domain_relation(
    d0_sv: &[String],
    d0_laws: &[PolyExpr],
    extra_pb_laws: &[PolyExpr],
    d0k_laws: &[PolyExpr],
    free_vars: &VarOrder,
    witness: &ParamWitness,
    eval_conds: &[&EvalCondition],
    coeff_domain: &CoeffDomain,
    point_domain: &PointDomain,
) -> Result<(DomainRelation, Vec<String>), SilenceReason> {
    let (order, bind) =
        ExprBindings::from_slices(d0_sv, &[], free_vars.vars()).map_err(map_algebra_silence)?;
    let param_bind = ExprBindings::params_only(free_vars);
    let state_count = d0_sv.len();

    let nonempty = is_ideal_nonempty(
        d0k_laws,
        d0_sv,
        &[],
        &IdealNonemptyCtx {
            free_vars,
            witness,
            eval_conds,
            coeff_domain,
            point_domain,
        },
    )?;

    let q_like = matches!(coeff_domain, CoeffDomain::Q)
        || (matches!(coeff_domain, CoeffDomain::Z)
            && matches!(
                point_domain,
                PointDomain::AlgebraicClosure | PointDomain::RationalPoints
            ));

    if q_like {
        let to_q = |list: &[PolyExpr]| -> Result<Vec<Poly<Rat>>, SilenceReason> {
            list.iter()
                .map(|e| Poly::from_expr_q(e, &bind).map_err(map_algebra_silence))
                .collect()
        };
        let mut d0_q = to_q(d0_laws)?;
        let mut d0k_q = to_q(d0k_laws)?;
        for nl in witness.remaining_nonlinear() {
            let lifted = nl.lift_vars(state_count);
            d0_q.push(lifted.clone());
            d0k_q.push(lifted);
        }
        let (ev_eqs, ev_invs) =
            collect_eval_and_extra(&[], eval_conds, &param_bind, Poly::from_expr_q)?;
        for eq in ev_eqs {
            let lifted = eq.lift_vars(state_count);
            d0_q.push(lifted.clone());
            d0k_q.push(lifted);
        }
        let ev_invs_lifted: Vec<Poly<Rat>> = ev_invs
            .into_iter()
            .map(|iv| iv.lift_vars(state_count))
            .collect();

        let d0k_gb = GroebnerBasis::compute(&d0k_q, order.clone(), MonomialOrder::Grevlex)
            .map_err(map_algebra_silence)?;
        let basis_owned: Vec<Poly<Rat>> = d0k_gb.basis_polys().into_iter().cloned().collect();
        let disp = display_polys(&basis_owned, &order);
        if !nonempty || d0k_gb.contains_one() {
            return Ok((
                DomainRelation::Empty,
                if disp.is_empty() {
                    vec!["1".to_owned()]
                } else {
                    disp
                },
            ));
        }
        if extra_pb_laws.is_empty() {
            return Ok((DomainRelation::FullIsomorphic, disp));
        }

        let d0_gens = if ev_invs_lifted.is_empty() {
            d0_q
        } else {
            let rab =
                rabinowitsch_solve(&d0_q, &ev_invs_lifted, &order).map_err(map_algebra_silence)?;
            if rab.is_empty_over_closure {
                return Ok((DomainRelation::Empty, vec!["1".to_owned()]));
            }
            rab.parameter_equations
        };
        let d0_gb = GroebnerBasis::compute(&d0_gens, order, MonomialOrder::Grevlex)
            .map_err(map_algebra_silence)?;
        if d0_gb.contains_one() {
            return Ok((DomainRelation::Empty, vec!["1".to_owned()]));
        }
        let extra_q = to_q(extra_pb_laws)?;
        let mut all_in_d0 = true;
        for ep in &extra_q {
            if !ep.is_zero() {
                let mem = d0_gb.membership(ep).map_err(map_algebra_silence)?;
                if !mem.is_member {
                    all_in_d0 = false;
                    break;
                }
            }
        }
        return Ok((
            if all_in_d0 {
                DomainRelation::FullIsomorphic
            } else {
                DomainRelation::ProperSubdomain
            },
            disp,
        ));
    }

    let disp = d0k_laws
        .iter()
        .filter_map(|e| fmt_poly_expr(e, &bind, &order, coeff_domain).ok())
        .filter(|s| s != "0")
        .collect::<Vec<_>>();
    if !nonempty {
        return Ok((
            DomainRelation::Empty,
            if disp.is_empty() {
                vec!["1".to_owned()]
            } else {
                disp
            },
        ));
    }
    if extra_pb_laws.is_empty() {
        return Ok((DomainRelation::FullIsomorphic, disp));
    }

    let all_in_d0 = match coeff_domain {
        CoeffDomain::Z => {
            let mut covered = true;
            for ex in extra_pb_laws {
                let ob = PreservationObligation {
                    state_vars: d0_sv.to_vec(),
                    arg_vars: vec![],
                    source_laws: d0_laws.to_vec(),
                    target: ex.clone(),
                };
                match decide_z_quotient_unit_safe(&ob, free_vars)? {
                    Some(true) => {}
                    Some(false) => {
                        covered = false;
                        break;
                    }
                    None => {
                        return Err(SilenceReason::QuotientIdealOutOfScope {
                            detail:
                                "cannot classify Z pullback domain relation outside unit-pivot scope"
                                    .to_owned(),
                        });
                    }
                }
            }
            covered
        }
        CoeffDomain::Fp(m) => {
            let mut covered = true;
            for ex in extra_pb_laws {
                let ob = PreservationObligation {
                    state_vars: d0_sv.to_vec(),
                    arg_vars: vec![],
                    source_laws: d0_laws.to_vec(),
                    target: ex.clone(),
                };
                match decide_fp_quotient_exact(&ob, m)? {
                    Some(true) => {}
                    Some(false) => {
                        covered = false;
                        break;
                    }
                    None => {
                        return Err(SilenceReason::QuotientIdealOutOfScope {
                            detail:
                                "cannot classify nonlinear multi-generator Fp pullback domain relation"
                                    .to_owned(),
                        });
                    }
                }
            }
            covered
        }
        CoeffDomain::Q => unreachable!("handled above"),
    };
    Ok((
        if all_in_d0 {
            DomainRelation::FullIsomorphic
        } else {
            DomainRelation::ProperSubdomain
        },
        disp,
    ))
}

pub(crate) fn append_composite_transfer_obligations(
    steps: &[TransferStepSpec],
    composed_h: &StateMorphism,
    composed_lift: &BTreeMap<String, PolyExpr>,
    d0k_laws: &[PolyExpr],
    re_obs: &mut Vec<PreservationObligation>,
) -> Result<(), SilenceReason> {
    if steps.len() < 2 {
        return Ok(());
    }
    let (d0_sv, _, _) = step_domain_env(&steps[0]);
    let last = steps.last().expect("last");
    let end_pres = &last.comparison.after;
    let start_pres = &steps[0].comparison.before;
    re_obs.extend(build_preservation_obligations(
        &composed_h.to_comparison_pair(end_pres, start_pres),
    )?);

    let tgt_ph = end_pres.phase(&last.target_phase).expect("target_phase");
    let empty = BTreeMap::new();
    for dc in &tgt_ph.coords {
        if let CoordValue::Observed(lit) = &dc.value
            && let Some(expr) = composed_lift.get(&dc.name)
        {
            re_obs.push(PreservationObligation {
                state_vars: d0_sv.clone(),
                arg_vars: vec![],
                source_laws: d0k_laws.to_vec(),
                target: PolyExpr::diff(expr.clone(), PolyExpr::Const(lit.clone())),
            });
        }
    }
    for tl in &tgt_ph.state_laws {
        re_obs.push(PreservationObligation {
            state_vars: d0_sv.clone(),
            arg_vars: vec![],
            source_laws: d0k_laws.to_vec(),
            target: substitute_poly_expr(&tl.polynomial, composed_lift, &empty, &empty),
        });
    }
    let sc = composed_h
        .state_comparisons
        .iter()
        .find(|s| s.after_phase == last.target_phase)
        .expect("composed sc");
    let start_ph = start_pres
        .phase(&steps[0].source_phase)
        .expect("source_phase");
    for c in &start_ph.coords {
        if let Some(h_expr) = sc.map.get(&c.name) {
            let h_of_m = substitute_poly_expr(h_expr, composed_lift, &empty, &empty);
            let iota = match &c.value {
                CoordValue::Observed(lit) => PolyExpr::Const(lit.clone()),
                CoordValue::Symbolic | CoordValue::Missing => PolyExpr::StateVar(c.name.clone()),
            };
            re_obs.push(PreservationObligation {
                state_vars: d0_sv.clone(),
                arg_vars: vec![],
                source_laws: d0k_laws.to_vec(),
                target: PolyExpr::diff(h_of_m, iota),
            });
        }
    }
    Ok(())
}

#[allow(clippy::type_complexity)]
pub(crate) fn format_restored_transfer(
    steps: &[TransferStepSpec],
    composed_h: &StateMorphism,
    step_lifts: &[(String, BTreeMap<String, PolyExpr>)],
    composed_lift: &BTreeMap<String, PolyExpr>,
    free_vars: &VarOrder,
    coeff_domain: &CoeffDomain,
) -> Result<
    (
        BTreeMap<String, BTreeMap<String, String>>,
        BTreeMap<String, Vec<String>>,
        BTreeMap<String, String>,
        Vec<(String, BTreeMap<String, String>)>,
    ),
    SilenceReason,
> {
    let (sc, wt) = format_state_morphism(
        composed_h,
        &steps.last().expect("last").comparison.after,
        free_vars.vars(),
    )?;
    let (d0_sv, _, _) = step_domain_env(&steps[0]);
    let (order_d0, bind_d0) =
        ExprBindings::from_slices(&d0_sv, &[], free_vars.vars()).map_err(map_algebra_silence)?;
    let mut cl = BTreeMap::new();
    for (k, expr) in composed_lift {
        cl.insert(
            k.clone(),
            fmt_poly_expr(expr, &bind_d0, &order_d0, coeff_domain)?,
        );
    }
    let mut sl = Vec::with_capacity(steps.len());
    for (step, (name, lmap)) in steps.iter().zip(step_lifts) {
        let (sv, _, _) = step_domain_env(step);
        let (order, bind) =
            ExprBindings::from_slices(&sv, &[], free_vars.vars()).map_err(map_algebra_silence)?;
        let mut fm = BTreeMap::new();
        for (k, expr) in lmap {
            fm.insert(k.clone(), fmt_poly_expr(expr, &bind, &order, coeff_domain)?);
        }
        sl.push((name.clone(), fm));
    }
    Ok((sc, wt, cl, sl))
}
