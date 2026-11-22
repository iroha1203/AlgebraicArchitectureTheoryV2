//! 状態移送後の共通操作語保存検算・旧側操作語 lift 探索（G-140 G2）。

use crate::algebra::{
    AffineSolutionZ, DEFAULT_MAX_FP_POINTS, ExprBindings, GroebnerBasis, MonomialOrder, Poly, Rat,
    VarOrder, solve_affine_z, solve_fp_enumeration,
};
use crate::ir::change::PointDomain;
use crate::ir::morphism::StateMorphism;
use crate::ir::presentation::{CoordValue, OperationDecl, Presentation, TranslatedStep};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::result_ext::{OldWordLiftResult, WordPreservationCheck};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::ir::transfer::{OldWordLiftSpec, TransferStepSpec, WordCheckSpec, WordStepExpr};
use crate::solver::common_format::fmt_poly_expr;
use crate::solver::common_solve::{ParamWitness, solve_obligations_and_evals};
use crate::solver::preservation::{
    PreservationObligation, map_algebra_silence, substitute_poly_expr,
};
use crate::solver::restore::polys_to_affine_system_z;
use crate::solver::transfer::step_domain_env;
use std::collections::BTreeMap;

const MAX_WORD_LIFT_SKELETONS: usize = 256;

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

/// 共通定義域・状態定義域イデアル `(laws)` が非空かを係数域・点域に従って判定する。
pub(crate) fn is_ideal_nonempty(
    laws: &[PolyExpr],
    state_vars: &[String],
    arg_vars: &[String],
    free_vars: &VarOrder,
    witness: &ParamWitness,
    coeff_domain: &CoeffDomain,
    point_domain: &PointDomain,
) -> Result<bool, SilenceReason> {
    let (order, bind) = ExprBindings::from_slices(state_vars, arg_vars, free_vars.vars())
        .map_err(map_algebra_silence)?;
    match coeff_domain {
        CoeffDomain::Q => {
            let mut polys: Vec<Poly<Rat>> = laws
                .iter()
                .map(|l| Poly::from_expr_q(l, &bind).map_err(map_algebra_silence))
                .collect::<Result<Vec<_>, _>>()?;
            let sa = state_vars.len() + arg_vars.len();
            for nl in witness.remaining_nonlinear() {
                polys.push(nl.lift_vars(sa));
            }
            let gb = GroebnerBasis::compute(&polys, order, MonomialOrder::Grevlex)
                .map_err(map_algebra_silence)?;
            Ok(!gb.contains_one())
        }
        CoeffDomain::Z => {
            let eqs_z: Vec<Poly<num_bigint::BigInt>> = laws
                .iter()
                .map(|l| Poly::from_expr_z(l, &bind).map_err(map_algebra_silence))
                .filter(|r| r.as_ref().map_or(true, |p| !p.is_zero()))
                .collect::<Result<Vec<_>, _>>()?;
            if *point_domain == PointDomain::IntegerPoints && eqs_z.iter().all(Poly::is_affine) {
                let (mat, rhs) = polys_to_affine_system_z(&eqs_z, order.len())?;
                return match solve_affine_z(&mat, &rhs, order.len()).map_err(map_algebra_silence)? {
                    AffineSolutionZ::Consistent { verified: true, .. } => Ok(true),
                    AffineSolutionZ::Inconsistent { verified: true, .. } => Ok(false),
                    _ => Err(SilenceReason::ApplicabilityConditionNotMet {
                        condition: "z_domain_nonempty".to_owned(),
                        detail: "Smith normal form check failed".to_owned(),
                    }),
                };
            }
            let eqs_q: Vec<Poly<Rat>> = eqs_z
                .iter()
                .map(crate::solver::common_solve::lift_z_to_q)
                .collect();
            let gb = GroebnerBasis::compute(&eqs_q, order, MonomialOrder::Grevlex)
                .map_err(map_algebra_silence)?;
            Ok(!gb.contains_one())
        }
        CoeffDomain::Fp(m) => {
            let polys: Vec<Poly<_>> = laws
                .iter()
                .map(|l| Poly::from_expr_fp(l, &bind, m).map_err(map_algebra_silence))
                .filter(|r| r.as_ref().map_or(true, |p| !p.is_zero()))
                .collect::<Result<Vec<_>, _>>()?;
            let res = solve_fp_enumeration(&polys, &[], order.len(), m, DEFAULT_MAX_FP_POINTS)?;
            Ok(!res.solutions.is_empty())
        }
    }
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
        coeff_domain,
        point_domain,
    )
}

#[allow(clippy::too_many_arguments)]
fn check_word_steps_impl(
    word_name: &str,
    word_args: &[String],
    steps: &[WordStepExpr],
    restored_steps: &[TransferStepSpec],
    composed_h: &StateMorphism,
    composed_lift: &BTreeMap<String, PolyExpr>,
    d0k_laws: &[PolyExpr],
    free_vars: &VarOrder,
    witness: &ParamWitness,
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
        free_vars,
        witness,
        coeff_domain,
        point_domain,
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
        state_comm = check_obs_vanish(&comm_obs, free_vars, witness, coeff_domain, point_domain)?;

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
        obs_pres = check_obs_vanish(&obs_obs, free_vars, witness, coeff_domain, point_domain)?;
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
    coeff_domain: &CoeffDomain,
    point_domain: &PointDomain,
) -> Result<bool, SilenceReason> {
    if obs.is_empty() {
        return Ok(true);
    }
    let res = solve_obligations_and_evals(obs, &[], &[], coeff_domain, point_domain, free_vars);
    match res.verdict {
        Verdict::Undetermined(r) => Err(r),
        Verdict::Refuted => Ok(false),
        Verdict::Established => {
            if !witness.remaining_nonlinear().is_empty() || !free_vars.is_empty() {
                let re = crate::solver::common_format::reeval_obligations_and_constraints(
                    obs,
                    &[],
                    &[],
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

/// 旧側操作語 `v` を移送後にも実行できる新語 `w`（`tau(w) = v` かつ `D_w` 非空）を独立探索する。
#[allow(clippy::too_many_arguments)]
pub(crate) fn search_old_word_lift(
    owl: &OldWordLiftSpec,
    restored_steps: &[TransferStepSpec],
    composed_h: &StateMorphism,
    composed_lift: &BTreeMap<String, PolyExpr>,
    d0k_laws: &[PolyExpr],
    param_subst: &BTreeMap<String, PolyExpr>,
    free_vars: &VarOrder,
    witness: &ParamWitness,
    coeff_domain: &CoeffDomain,
    point_domain: &PointDomain,
) -> Result<OldWordLiftResult, SilenceReason> {
    let max_len = owl.max_length.expect("checked finite max_length");
    let x0_pres = &restored_steps[0].comparison.before;
    let xk_pres = &restored_steps.last().expect("last").comparison.after;
    let x0_start_phase = restored_steps[0].source_phase.as_str();
    let xk_start_phase = restored_steps.last().expect("last").target_phase.as_str();
    let (d0_sv, _, _) = step_domain_env(&restored_steps[0]);
    let empty = BTreeMap::new();

    let target_steps: Vec<WordStepExpr> = owl
        .target_steps
        .iter()
        .map(|s| substitute_word_step(s, param_subst))
        .collect();
    let (order_v, bind_v) = ExprBindings::from_slices(&d0_sv, &owl.args, free_vars.vars())
        .map_err(map_algebra_silence)?;
    let target_disp = format_word_steps(&target_steps, &bind_v, &order_v, coeff_domain)?;

    let mut base_dw_laws = d0k_laws.to_vec();
    let x0_ph = x0_pres.phase(x0_start_phase).expect("x0 start phase");
    let mut old_state: BTreeMap<String, PolyExpr> = x0_ph
        .coords
        .iter()
        .map(|c| match &c.value {
            CoordValue::Observed(lit) => (c.name.clone(), PolyExpr::Const(lit.clone())),
            CoordValue::Symbolic | CoordValue::Missing => {
                (c.name.clone(), PolyExpr::StateVar(c.name.clone()))
            }
        })
        .collect();
    for st in &target_steps {
        let bop = x0_pres.operation(&st.operation).expect("checked bop");
        let b_arg: BTreeMap<String, PolyExpr> = bop
            .args
            .iter()
            .zip(&st.arg_exprs)
            .map(|((n, _), e)| (n.clone(), e.clone()))
            .collect();
        for dl in &bop.domain_laws {
            base_dw_laws.push(substitute_poly_expr(
                &dl.polynomial,
                &old_state,
                &b_arg,
                &empty,
            ));
        }
        let mut next_old = BTreeMap::new();
        for (coord, upd) in &bop.updates {
            next_old.insert(
                coord.clone(),
                substitute_poly_expr(upd, &old_state, &b_arg, &empty),
            );
        }
        old_state = next_old;
    }

    let target_op_names: Vec<&str> = target_steps.iter().map(|s| s.operation.as_str()).collect();
    let skeletons = enumerate_matching_skeletons(
        xk_pres,
        xk_start_phase,
        composed_h,
        &target_op_names,
        max_len,
    )?;

    let base_dw_disp: Vec<String> = base_dw_laws
        .iter()
        .filter_map(|e| fmt_poly_expr(e, &bind_v, &order_v, coeff_domain).ok())
        .filter(|s| s != "0")
        .collect();

    let mut first_undetermined: Option<SilenceReason> = None;
    for sk in skeletons {
        match try_solve_skeleton_lift(
            &sk,
            &target_steps,
            &owl.args,
            &d0_sv,
            &base_dw_laws,
            restored_steps,
            composed_h,
            composed_lift,
            d0k_laws,
            free_vars,
            witness,
            coeff_domain,
            point_domain,
        ) {
            Ok(Some((lifted_steps, wcheck))) => {
                let lifted_disp =
                    format_word_steps(&lifted_steps, &bind_v, &order_v, coeff_domain)?;
                let detail = format!(
                    "found lifted new word `{}` matching old word `{}`",
                    lifted_disp.join("; "),
                    owl.name
                );
                return Ok(OldWordLiftResult {
                    check_name: owl.name.clone(),
                    target_old_word: target_disp,
                    lift_found: true,
                    lifted_new_word: Some(lifted_disp),
                    common_domain_equations: wcheck.common_domain_equations,
                    detail,
                });
            }
            Ok(None) => {}
            Err(r) => {
                if first_undetermined.is_none() {
                    first_undetermined = Some(r);
                }
            }
        }
    }

    if let Some(r) = first_undetermined {
        return Err(r);
    }

    Ok(OldWordLiftResult {
        check_name: owl.name.clone(),
        target_old_word: target_disp,
        lift_found: false,
        lifted_new_word: None,
        common_domain_equations: base_dw_disp,
        detail: format!(
            "no lifted new word up to length {max_len} matching `{}` exists within D_0",
            owl.name
        ),
    })
}

fn enumerate_matching_skeletons<'a>(
    pres: &'a Presentation,
    start_phase: &str,
    composed_h: &StateMorphism,
    target_ops: &[&str],
    max_len: usize,
) -> Result<Vec<Vec<&'a OperationDecl>>, SilenceReason> {
    let mut out = Vec::new();
    let mut frontier_count = 0usize;
    let mut stack: Vec<(&str, usize, Vec<&'a OperationDecl>)> = vec![(start_phase, 0, Vec::new())];
    while let Some((cur_ph, matched, seq)) = stack.pop() {
        if matched == target_ops.len() {
            out.push(seq.clone());
            if out.len() > MAX_WORD_LIFT_SKELETONS {
                return Err(SilenceReason::UnboundedSearchOutOfScope {
                    detail: format!(
                        "old word lift skeleton count exceeded {MAX_WORD_LIFT_SKELETONS}"
                    ),
                });
            }
        }
        if seq.len() == max_len {
            continue;
        }
        for op in pres.operations.iter().rev() {
            if op.source_phase != cur_ph {
                continue;
            }
            let Some(tw) = composed_h.word_translation.for_operation(&op.name) else {
                continue;
            };
            if matched + tw.steps.len() > target_ops.len() {
                continue;
            }
            let prefix_ok = tw
                .steps
                .iter()
                .enumerate()
                .all(|(i, ts)| ts.before_operation == target_ops[matched + i]);
            if !prefix_ok {
                continue;
            }
            frontier_count += 1;
            if frontier_count > MAX_WORD_LIFT_SKELETONS * 8 {
                return Err(SilenceReason::UnboundedSearchOutOfScope {
                    detail: format!(
                        "old word lift search frontier exceeded {MAX_WORD_LIFT_SKELETONS}"
                    ),
                });
            }
            let mut next = seq.clone();
            next.push(op);
            stack.push((op.target_phase.as_str(), matched + tw.steps.len(), next));
        }
    }
    out.sort_by(|a, b| {
        a.len()
            .cmp(&b.len())
            .then_with(|| a.iter().map(|o| &o.name).cmp(b.iter().map(|o| &o.name)))
    });
    Ok(out)
}

#[allow(clippy::too_many_arguments, clippy::type_complexity)]
fn try_solve_skeleton_lift(
    skeleton: &[&OperationDecl],
    target_steps: &[WordStepExpr],
    word_args: &[String],
    d0_sv: &[String],
    base_dw_laws: &[PolyExpr],
    restored_steps: &[TransferStepSpec],
    composed_h: &StateMorphism,
    composed_lift: &BTreeMap<String, PolyExpr>,
    d0k_laws: &[PolyExpr],
    free_vars: &VarOrder,
    witness: &ParamWitness,
    coeff_domain: &CoeffDomain,
    point_domain: &PointDomain,
) -> Result<Option<(Vec<WordStepExpr>, WordPreservationCheck)>, SilenceReason> {
    if !free_vars.is_empty() {
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "ground_transfer_required_for_word_lift".to_owned(),
            detail: "old word lift search with uninstantiated change parameters is out of scope"
                .to_owned(),
        });
    }
    let empty = BTreeMap::new();
    let mut coeff_names = Vec::new();
    let mut step_arg_templates: Vec<Vec<(String, Vec<(String, PolyExpr)>)>> =
        Vec::with_capacity(skeleton.len());
    let mut c_idx = 0usize;

    let zero_lit = || match coeff_domain {
        CoeffDomain::Z => PolyExpr::Const(ScalarLit::int(0)),
        CoeffDomain::Q => PolyExpr::rat(0, 1).expect("0/1"),
        CoeffDomain::Fp(m) => {
            PolyExpr::Const(ScalarLit::fp(num_bigint::BigInt::from(0), m.clone()).expect("fp 0"))
        }
    };
    let one_lit = match coeff_domain {
        CoeffDomain::Z => PolyExpr::Const(ScalarLit::int(1)),
        CoeffDomain::Q => PolyExpr::rat(1, 1).expect("1/1"),
        CoeffDomain::Fp(m) => {
            PolyExpr::Const(ScalarLit::fp(num_bigint::BigInt::from(1), m.clone()).expect("fp 1"))
        }
    };

    let mut basis: Vec<PolyExpr> = vec![one_lit];
    for s in d0_sv {
        basis.push(PolyExpr::StateVar(s.clone()));
    }
    for a in word_args {
        basis.push(PolyExpr::ArgVar(a.clone()));
    }

    for op in skeleton {
        let mut op_tpl = Vec::with_capacity(op.args.len());
        for (a, _) in &op.args {
            let mut terms = Vec::with_capacity(basis.len());
            for b in &basis {
                let cname = format!("__lift_c_{c_idx}");
                c_idx += 1;
                coeff_names.push(cname.clone());
                terms.push((cname, b.clone()));
            }
            op_tpl.push((a.clone(), terms));
        }
        step_arg_templates.push(op_tpl);
    }

    let lift_param_vars = VarOrder::new(coeff_names).map_err(map_algebra_silence)?;
    let mut obs = Vec::new();
    let mut cur_state = composed_lift.clone();
    let mut target_cursor = 0usize;

    for (op, tpl) in skeleton.iter().zip(&step_arg_templates) {
        let mut arg_map = BTreeMap::new();
        for (a, terms) in tpl {
            let mut e = zero_lit();
            for (cn, b) in terms {
                e = PolyExpr::sum(e, PolyExpr::prod(PolyExpr::ParamVar(cn.clone()), b.clone()));
            }
            arg_map.insert(a.clone(), e);
        }
        for dl in &op.domain_laws {
            obs.push(PreservationObligation {
                state_vars: d0_sv.to_vec(),
                arg_vars: word_args.to_vec(),
                source_laws: base_dw_laws.to_vec(),
                target: substitute_poly_expr(&dl.polynomial, &cur_state, &arg_map, &empty),
            });
        }
        let tw = composed_h
            .word_translation
            .for_operation(&op.name)
            .expect("tw exists");
        for ts in &tw.steps {
            let tgt = &target_steps[target_cursor];
            target_cursor += 1;
            for (ae, te) in ts.arg_exprs.iter().zip(&tgt.arg_exprs) {
                let eval_ae = substitute_poly_expr(ae, &cur_state, &arg_map, &empty);
                obs.push(PreservationObligation {
                    state_vars: d0_sv.to_vec(),
                    arg_vars: word_args.to_vec(),
                    source_laws: base_dw_laws.to_vec(),
                    target: PolyExpr::diff(eval_ae, te.clone()),
                });
            }
        }
        let mut next_state = BTreeMap::new();
        for (coord, upd) in &op.updates {
            next_state.insert(
                coord.clone(),
                substitute_poly_expr(upd, &cur_state, &arg_map, &empty),
            );
        }
        cur_state = next_state;
    }

    let solve =
        solve_obligations_and_evals(&obs, &[], &[], coeff_domain, point_domain, &lift_param_vars);
    let lift_witness = match solve.verdict {
        Verdict::Undetermined(r) => return Err(r),
        Verdict::Refuted => return Ok(None),
        Verdict::Established => solve.witness.expect("witness"),
    };
    let raw_subst = lift_witness.to_param_subst(&lift_param_vars);
    let zero_map: BTreeMap<String, PolyExpr> = lift_witness
        .unassigned_parameters()
        .into_iter()
        .map(|rem| (rem, zero_lit()))
        .collect();
    let mut subst = BTreeMap::new();
    for (k, expr) in &raw_subst {
        subst.insert(
            k.clone(),
            substitute_poly_expr(expr, &empty, &empty, &zero_map),
        );
    }
    for (k, v) in zero_map {
        subst.insert(k, v);
    }
    if !lift_witness.remaining_nonlinear().is_empty() {
        let sub_obs: Vec<PreservationObligation> = obs
            .iter()
            .map(|o| PreservationObligation {
                state_vars: o.state_vars.clone(),
                arg_vars: o.arg_vars.clone(),
                source_laws: o
                    .source_laws
                    .iter()
                    .map(|l| substitute_poly_expr(l, &empty, &empty, &subst))
                    .collect(),
                target: substitute_poly_expr(&o.target, &empty, &empty, &subst),
            })
            .collect();
        let zero_vars = VarOrder::new(vec![]).map_err(map_algebra_silence)?;
        let verify =
            solve_obligations_and_evals(&sub_obs, &[], &[], coeff_domain, point_domain, &zero_vars);
        match verify.verdict {
            Verdict::Established => {}
            Verdict::Refuted => return Ok(None),
            Verdict::Undetermined(r) => return Err(r),
        }
    }

    let mut candidate_steps = Vec::with_capacity(skeleton.len());
    for (op, tpl) in skeleton.iter().zip(&step_arg_templates) {
        let mut arg_exprs = Vec::with_capacity(tpl.len());
        for (_, terms) in tpl {
            let mut raw = zero_lit();
            for (cn, b) in terms {
                raw = PolyExpr::sum(
                    raw,
                    PolyExpr::prod(PolyExpr::ParamVar(cn.clone()), b.clone()),
                );
            }
            arg_exprs.push(substitute_poly_expr(&raw, &empty, &empty, &subst));
        }
        candidate_steps.push(WordStepExpr {
            operation: op.name.clone(),
            arg_exprs,
        });
    }

    let check = check_word_steps_impl(
        "__lift_candidate",
        word_args,
        &candidate_steps,
        restored_steps,
        composed_h,
        composed_lift,
        d0k_laws,
        free_vars,
        witness,
        coeff_domain,
        point_domain,
    )?;
    if check.domain_nonempty && check.state_commutativity_matched && check.observation_preserved {
        Ok(Some((candidate_steps, check)))
    } else {
        Ok(None)
    }
}

fn substitute_word_step(
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

fn format_word_steps(
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
