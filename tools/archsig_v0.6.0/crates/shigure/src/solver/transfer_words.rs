//! 状態移送後の共通操作語保存検算・補助表示ヘルパ（G-140 G2）。

use crate::algebra::{ExprBindings, GroebnerBasis, MonomialOrder, Poly, Rat, VarOrder};
use crate::ir::change::{EvalCondition, PointDomain};
use crate::ir::morphism::StateMorphism;
use crate::ir::presentation::{CoordValue, TranslatedStep};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::result_ext::WordPreservationCheck;
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::ir::transfer::{TransferStepSpec, WordCheckSpec, WordStepExpr};
use crate::solver::common_format::{
    fmt_poly_expr, poly_q_to_expr, reeval_obligations_and_constraints,
};
use crate::solver::common_solve::{ParamWitness, solve_obligations_and_evals};
use crate::solver::common_solve_q::{IdealNonemptyCtx, is_ideal_nonempty};
use crate::solver::preservation::{
    PreservationObligation, map_algebra_silence, substitute_poly_expr,
};
use crate::solver::transfer::step_domain_env;
use std::collections::BTreeMap;

/// 単一の多項式義務 `target` を `source_laws` で簡約して表示（可換・step 診断用）。
pub(crate) fn eval_poly_q_or_format(
    target: &PolyExpr,
    source_laws: &[PolyExpr],
    state_vars: &[String],
    arg_vars: &[String],
    param_vars: &VarOrder,
    domain: &CoeffDomain,
) -> Result<String, SilenceReason> {
    let (order, bind) = ExprBindings::from_slices(state_vars, arg_vars, param_vars.vars())
        .map_err(map_algebra_silence)?;
    if matches!(domain, CoeffDomain::Q | CoeffDomain::Z) && !source_laws.is_empty() {
        let ql: Result<Vec<Poly<Rat>>, _> = source_laws
            .iter()
            .map(|l| Poly::from_expr_q(l, &bind))
            .collect();
        if let Ok(laws) = ql
            && let Ok(gb) = GroebnerBasis::compute(&laws, order.clone(), MonomialOrder::Grevlex)
        {
            if gb.contains_one() {
                return Ok("0".to_owned());
            }
            let tp = Poly::from_expr_q(target, &bind).map_err(map_algebra_silence)?;
            let nf = gb.normal_form(&tp).map_err(map_algebra_silence)?;
            return Ok(nf.display(&order, MonomialOrder::Grevlex));
        }
    }
    fmt_poly_expr(target, &bind, &order, domain)
}

/// 新側許可語 $w$ について共通定義域 $D_w$ 上の状態可換性と観測保存を検算する。
#[allow(clippy::too_many_arguments)]
pub(crate) fn check_word_preservation(
    wc: &WordCheckSpec,
    restored_steps: &[TransferStepSpec],
    composed_h: &StateMorphism,
    composed_lift: &BTreeMap<String, PolyExpr>,
    d0k_laws: &[PolyExpr],
    param_subst: &BTreeMap<String, PolyExpr>,
    free_vars: &VarOrder,
    witness: &ParamWitness,
    eval_conds: &[&EvalCondition],
    coeff_domain: &CoeffDomain,
    point_domain: &PointDomain,
) -> Result<WordPreservationCheck, SilenceReason> {
    let steps_sub: Vec<WordStepExpr> = wc
        .steps
        .iter()
        .map(|st| substitute_word_step(st, param_subst))
        .collect();
    check_word_steps_impl(
        &wc.name,
        &wc.args,
        &steps_sub,
        restored_steps,
        composed_h,
        composed_lift,
        d0k_laws,
        free_vars,
        witness,
        eval_conds,
        coeff_domain,
        point_domain,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn check_word_steps_impl(
    word_name: &str,
    word_args: &[String],
    steps: &[WordStepExpr],
    restored_steps: &[TransferStepSpec],
    composed_h: &StateMorphism,
    composed_lift: &BTreeMap<String, PolyExpr>,
    d0k_laws: &[PolyExpr],
    free_vars: &VarOrder,
    witness: &ParamWitness,
    eval_conds: &[&EvalCondition],
    coeff_domain: &CoeffDomain,
    point_domain: &PointDomain,
) -> Result<WordPreservationCheck, SilenceReason> {
    let empty = BTreeMap::new();
    let x0_pres = &restored_steps[0].comparison.before;
    let xk_pres = &restored_steps.last().expect("last").comparison.after;
    let x0_start_phase = restored_steps[0].source_phase.as_str();
    let xk_start_phase = restored_steps.last().expect("last").target_phase.as_str();
    let (d0_sv, d0_obs, _) = step_domain_env(&restored_steps[0]);

    let mut dw_laws = d0k_laws.to_vec();
    let mut new_state = composed_lift.clone();
    let mut cur_new_phase = xk_start_phase;
    let mut translated_steps = Vec::new();

    let (arg_order_new, arg_bind_new) =
        ExprBindings::from_slices(&d0_sv, word_args, free_vars.vars())
            .map_err(map_algebra_silence)?;
    let new_word_disp = format_word_steps(steps, &arg_bind_new, &arg_order_new, coeff_domain)?;

    for st in steps {
        let op = xk_pres.operation(&st.operation).ok_or_else(|| {
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "word_operation_present".to_owned(),
                detail: format!("unknown operation `{}`", st.operation),
            }
        })?;
        let mut op_arg_map = BTreeMap::new();
        for ((aname, _), expr) in op.args.iter().zip(&st.arg_exprs) {
            op_arg_map.insert(aname.clone(), expr.clone());
        }
        for dl in &op.domain_laws {
            dw_laws.push(substitute_poly_expr(
                &dl.polynomial,
                &new_state,
                &op_arg_map,
                &empty,
            ));
        }

        let tw = composed_h
            .word_translation
            .for_operation(&st.operation)
            .ok_or_else(|| SilenceReason::ApplicabilityConditionNotMet {
                condition: "word_translation_present".to_owned(),
                detail: format!("missing translation for `{}`", st.operation),
            })?;
        for ts in &tw.steps {
            let t_args: Vec<PolyExpr> = ts
                .arg_exprs
                .iter()
                .map(|ae| substitute_poly_expr(ae, &new_state, &op_arg_map, &empty))
                .collect();
            translated_steps.push(TranslatedStep {
                before_operation: ts.before_operation.clone(),
                arg_exprs: t_args,
            });
        }

        let mut next_new = BTreeMap::new();
        for (coord, upd) in &op.updates {
            next_new.insert(
                coord.clone(),
                substitute_poly_expr(upd, &new_state, &op_arg_map, &empty),
            );
        }
        new_state = next_new;
        cur_new_phase = op.target_phase.as_str();
    }

    let x0_start_ph = x0_pres.phase(x0_start_phase).expect("start phase");
    let mut old_state: BTreeMap<String, PolyExpr> = x0_start_ph
        .coords
        .iter()
        .map(|c| match &c.value {
            CoordValue::Observed(lit) => (c.name.clone(), PolyExpr::Const(lit.clone())),
            CoordValue::Symbolic | CoordValue::Missing => {
                (c.name.clone(), PolyExpr::StateVar(c.name.clone()))
            }
        })
        .collect();
    let _ = d0_obs;
    let mut cur_old_phase = x0_start_phase;

    for ts in &translated_steps {
        let bop = x0_pres.operation(&ts.before_operation).ok_or_else(|| {
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "translated_before_operation_present".to_owned(),
                detail: format!("missing before operation `{}`", ts.before_operation),
            }
        })?;
        let mut b_arg_map = BTreeMap::new();
        for ((aname, _), expr) in bop.args.iter().zip(&ts.arg_exprs) {
            b_arg_map.insert(aname.clone(), expr.clone());
        }
        for dl in &bop.domain_laws {
            dw_laws.push(substitute_poly_expr(
                &dl.polynomial,
                &old_state,
                &b_arg_map,
                &empty,
            ));
        }
        let mut next_old = BTreeMap::new();
        for (coord, upd) in &bop.updates {
            next_old.insert(
                coord.clone(),
                substitute_poly_expr(upd, &old_state, &b_arg_map, &empty),
            );
        }
        old_state = next_old;
        cur_old_phase = bop.target_phase.as_str();
    }

    let translated_disp = format_translated_steps(
        &translated_steps,
        &arg_bind_new,
        &arg_order_new,
        coeff_domain,
    )?;
    let dw_disp: Vec<String> = dw_laws
        .iter()
        .filter_map(|e| fmt_poly_expr(e, &arg_bind_new, &arg_order_new, coeff_domain).ok())
        .filter(|s| s != "0")
        .collect();

    let domain_nonempty = is_ideal_nonempty(
        &dw_laws,
        &d0_sv,
        word_args,
        &IdealNonemptyCtx {
            free_vars,
            witness,
            eval_conds,
            coeff_domain,
            point_domain,
        },
    )?;
    if !domain_nonempty {
        return Ok(WordPreservationCheck {
            word_name: word_name.to_owned(),
            new_word: new_word_disp,
            translated_old_word: translated_disp,
            common_domain_equations: dw_disp,
            domain_nonempty: false,
            state_commutativity_matched: false,
            observation_preserved: false,
            detail: format!("common domain D_w for `{word_name}` is empty"),
        });
    }

    let sc_end = composed_h
        .state_comparisons
        .iter()
        .find(|s| s.after_phase == cur_new_phase)
        .expect("sc for cur_new_phase");
    let mut state_comm = sc_end.before_phase == cur_old_phase;
    let mut obs_pres = sc_end.before_phase == cur_old_phase;
    if state_comm {
        let mut comm_obs = Vec::new();
        for (coord, h_expr) in &sc_end.map {
            let lhs = substitute_poly_expr(h_expr, &new_state, &empty, &empty);
            let rhs = old_state.get(coord).ok_or_else(|| {
                SilenceReason::ApplicabilityConditionNotMet {
                    condition: "old_word_coord_present".to_owned(),
                    detail: format!("missing old state coord `{coord}`"),
                }
            })?;
            comm_obs.push(PreservationObligation {
                state_vars: d0_sv.clone(),
                arg_vars: word_args.to_vec(),
                source_laws: dw_laws.clone(),
                target: PolyExpr::diff(lhs, rhs.clone()),
            });
        }
        state_comm = check_obs_vanish(
            &comm_obs,
            free_vars,
            witness,
            eval_conds,
            coeff_domain,
            point_domain,
        )?;

        let mut obs_obs = Vec::new();
        let x0_obs_map: BTreeMap<&str, _> = x0_pres
            .observations
            .iter()
            .filter(|o| o.phase == cur_old_phase)
            .map(|o| (o.name.as_str(), o))
            .collect();
        for new_obs in xk_pres
            .observations
            .iter()
            .filter(|o| o.phase == cur_new_phase)
        {
            if let Some(old_obs) = x0_obs_map.get(new_obs.name.as_str()) {
                for (nc, oc) in new_obs.components.iter().zip(&old_obs.components) {
                    let lhs = substitute_poly_expr(nc, &new_state, &empty, &empty);
                    let rhs = substitute_poly_expr(oc, &old_state, &empty, &empty);
                    obs_obs.push(PreservationObligation {
                        state_vars: d0_sv.clone(),
                        arg_vars: word_args.to_vec(),
                        source_laws: dw_laws.clone(),
                        target: PolyExpr::diff(lhs, rhs),
                    });
                }
            }
        }
        obs_pres = check_obs_vanish(
            &obs_obs,
            free_vars,
            witness,
            eval_conds,
            coeff_domain,
            point_domain,
        )?;
    }

    Ok(WordPreservationCheck {
        word_name: word_name.to_owned(),
        new_word: new_word_disp,
        translated_old_word: translated_disp,
        common_domain_equations: dw_disp,
        domain_nonempty: true,
        state_commutativity_matched: state_comm,
        observation_preserved: obs_pres,
        detail: if state_comm && obs_pres {
            format!(
                "verified word `{word_name}` commutativity and observation preservation on nonempty D_w"
            )
        } else {
            format!("word `{word_name}` failed state commutativity or observation preservation")
        },
    })
}

fn check_obs_vanish(
    obs: &[PreservationObligation],
    free_vars: &VarOrder,
    witness: &ParamWitness,
    eval_conds: &[&EvalCondition],
    coeff_domain: &CoeffDomain,
    point_domain: &PointDomain,
) -> Result<bool, SilenceReason> {
    if obs.is_empty() {
        return Ok(true);
    }
    let extra_nl: Vec<PolyExpr> = if matches!(coeff_domain, CoeffDomain::Q)
        || (matches!(coeff_domain, CoeffDomain::Z) && *point_domain != PointDomain::IntegerPoints)
    {
        witness
            .remaining_nonlinear()
            .iter()
            .map(|p| poly_q_to_expr(p, free_vars))
            .collect()
    } else {
        vec![]
    };
    let res = solve_obligations_and_evals(
        obs,
        &extra_nl,
        eval_conds,
        coeff_domain,
        point_domain,
        free_vars,
    );
    match res.verdict {
        Verdict::Undetermined(r) => Err(r),
        Verdict::Refuted => Ok(false),
        Verdict::Established => {
            if !witness.remaining_nonlinear().is_empty() || !free_vars.is_empty() {
                let re = reeval_obligations_and_constraints(
                    obs,
                    &[],
                    eval_conds,
                    witness,
                    coeff_domain,
                    point_domain,
                    "word_check",
                )?;
                return Ok(re.matched);
            }
            Ok(true)
        }
    }
}

pub(crate) fn substitute_word_step(
    st: &WordStepExpr,
    param_subst: &BTreeMap<String, PolyExpr>,
) -> WordStepExpr {
    let empty = BTreeMap::new();
    WordStepExpr {
        operation: st.operation.clone(),
        arg_exprs: st
            .arg_exprs
            .iter()
            .map(|e| substitute_poly_expr(e, &empty, &empty, param_subst))
            .collect(),
    }
}

pub(crate) fn format_word_steps(
    steps: &[WordStepExpr],
    bind: &ExprBindings,
    order: &VarOrder,
    domain: &CoeffDomain,
) -> Result<Vec<String>, SilenceReason> {
    let mut out = Vec::with_capacity(steps.len());
    for st in steps {
        let mut args = Vec::with_capacity(st.arg_exprs.len());
        for a in &st.arg_exprs {
            args.push(fmt_poly_expr(a, bind, order, domain)?);
        }
        if args.is_empty() {
            out.push(st.operation.clone());
        } else {
            out.push(format!("{}({})", st.operation, args.join(", ")));
        }
    }
    Ok(out)
}

fn format_translated_steps(
    steps: &[TranslatedStep],
    bind: &ExprBindings,
    order: &VarOrder,
    domain: &CoeffDomain,
) -> Result<Vec<String>, SilenceReason> {
    let mut out = Vec::with_capacity(steps.len());
    for st in steps {
        let mut args = Vec::with_capacity(st.arg_exprs.len());
        for a in &st.arg_exprs {
            args.push(fmt_poly_expr(a, bind, order, domain)?);
        }
        if args.is_empty() {
            out.push(st.before_operation.clone());
        } else {
            out.push(format!("{}({})", st.before_operation, args.join(", ")));
        }
    }
    Ok(out)
}
