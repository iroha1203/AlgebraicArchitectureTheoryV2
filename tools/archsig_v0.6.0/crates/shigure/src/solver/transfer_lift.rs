//! 旧側操作語の有限長 lift 探索と多項式引数合成（G-140 G2）。

use crate::algebra::{ExprBindings, VarOrder};
use crate::ir::change::{EvalCondition, PointDomain};
use crate::ir::morphism::StateMorphism;
use crate::ir::presentation::{CoordValue, OperationDecl, Presentation};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::result_ext::{OldWordLiftResult, WordPreservationCheck};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::ir::transfer::{OldWordLiftSpec, TransferStepSpec, WordStepExpr};
use crate::solver::common_solve::ParamWitness;
use crate::solver::common_solve::solve_obligations_and_evals;
use crate::solver::preservation::{
    PreservationObligation, map_algebra_silence, substitute_poly_expr,
};
use crate::solver::transfer::step_domain_env;
use crate::solver::transfer_words::{
    check_word_steps_impl, format_word_steps, substitute_word_step,
};
use std::collections::BTreeMap;

const MAX_WORD_LIFT_SKELETONS: usize = 256;
const MAX_LIFT_BASIS_TERMS: usize = 28;

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
    eval_conds: &[&EvalCondition],
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
        .filter_map(|e| {
            crate::solver::common_format::fmt_poly_expr(e, &bind_v, &order_v, coeff_domain).ok()
        })
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
            eval_conds,
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

fn poly_expr_degree(expr: &PolyExpr) -> u64 {
    let mut stack = vec![(expr, false)];
    let mut vals: Vec<u64> = Vec::new();
    while let Some((node, visited)) = stack.pop() {
        if !visited {
            match node {
                PolyExpr::Const(_) | PolyExpr::ParamVar(_) | PolyExpr::Unobserved { .. } => {
                    vals.push(0);
                }
                PolyExpr::StateVar(_) | PolyExpr::ArgVar(_) => {
                    vals.push(1);
                }
                PolyExpr::Neg(a) | PolyExpr::Pow(a, _) => {
                    stack.push((node, true));
                    stack.push((a, false));
                }
                PolyExpr::Add(a, b) | PolyExpr::Sub(a, b) | PolyExpr::Mul(a, b) => {
                    stack.push((node, true));
                    stack.push((b, false));
                    stack.push((a, false));
                }
            }
        } else {
            match node {
                PolyExpr::Neg(_) => {}
                PolyExpr::Pow(_, k) => {
                    let top = vals.pop().expect("degree");
                    vals.push(top.saturating_mul(u64::from(*k)));
                }
                PolyExpr::Add(_, _) | PolyExpr::Sub(_, _) => {
                    let b = vals.pop().expect("rhs");
                    let a = vals.pop().expect("lhs");
                    vals.push(a.max(b));
                }
                PolyExpr::Mul(_, _) => {
                    let b = vals.pop().expect("rhs");
                    let a = vals.pop().expect("lhs");
                    vals.push(a.saturating_add(b));
                }
                PolyExpr::Const(_)
                | PolyExpr::StateVar(_)
                | PolyExpr::ArgVar(_)
                | PolyExpr::ParamVar(_)
                | PolyExpr::Unobserved { .. } => {}
            }
        }
    }
    vals.pop().unwrap_or(0)
}

fn collect_monomials(
    vars: &[PolyExpr],
    start: usize,
    rem_deg: usize,
    depth: usize,
    combo: &mut [usize],
    out: &mut Vec<PolyExpr>,
) {
    if out.len() > MAX_LIFT_BASIS_TERMS {
        return;
    }
    if depth == rem_deg {
        let mut prod = vars[combo[0]].clone();
        for &idx in &combo[1..rem_deg] {
            prod = PolyExpr::prod(prod, vars[idx].clone());
        }
        out.push(prod);
        return;
    }
    for i in start..vars.len() {
        combo[depth] = i;
        collect_monomials(vars, i, rem_deg, depth + 1, combo, out);
    }
}

fn build_lift_basis(
    d0_sv: &[String],
    word_args: &[String],
    target_deg: u64,
    one_lit: &PolyExpr,
) -> (Vec<PolyExpr>, u64, bool) {
    let mut vars: Vec<PolyExpr> = Vec::with_capacity(d0_sv.len() + word_args.len());
    for s in d0_sv {
        vars.push(PolyExpr::StateVar(s.clone()));
    }
    for a in word_args {
        vars.push(PolyExpr::ArgVar(a.clone()));
    }
    let mut basis = vec![one_lit.clone()];
    let mut achieved = 0u64;
    let max_deg = target_deg.clamp(1, 4) as usize;
    for deg in 1..=max_deg {
        if vars.is_empty() {
            break;
        }
        let mut deg_terms = Vec::new();
        let mut combo = vec![0usize; deg];
        collect_monomials(&vars, 0, deg, 0, &mut combo, &mut deg_terms);
        if basis.len() + deg_terms.len() > MAX_LIFT_BASIS_TERMS {
            break;
        }
        basis.extend(deg_terms);
        achieved = deg as u64;
    }
    (basis, achieved, vars.is_empty())
}

fn grid_candidates(ar: usize) -> Vec<Vec<i64>> {
    match ar {
        0 => vec![vec![]],
        1 => vec![vec![0], vec![1], vec![-1], vec![2], vec![-2]],
        2 => {
            let vals = [0i64, 1, -1, 2, -2];
            let mut out = Vec::with_capacity(25);
            for a in vals {
                for b in vals {
                    out.push(vec![a, b]);
                }
            }
            out
        }
        3 => {
            let vals = [0i64, 1, -1];
            let mut out = Vec::with_capacity(27);
            for a in vals {
                for b in vals {
                    for c in vals {
                        out.push(vec![a, b, c]);
                    }
                }
            }
            out
        }
        _ => vec![],
    }
}

fn domain_int_lit(coeff_domain: &CoeffDomain, n: i64) -> PolyExpr {
    match coeff_domain {
        CoeffDomain::Z => PolyExpr::Const(ScalarLit::int(n)),
        CoeffDomain::Q => PolyExpr::rat(n, 1).expect("n/1"),
        CoeffDomain::Fp(m) => {
            PolyExpr::Const(ScalarLit::fp(num_bigint::BigInt::from(n), m.clone()).expect("fp"))
        }
    }
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
    eval_conds: &[&EvalCondition],
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
    let max_target_deg = target_steps
        .iter()
        .flat_map(|s| s.arg_exprs.iter())
        .map(poly_expr_degree)
        .max()
        .unwrap_or(0)
        .max(1);
    let zero_lit = || domain_int_lit(coeff_domain, 0);
    let one_lit = domain_int_lit(coeff_domain, 1);
    let (basis, achieved_deg, no_state_args) =
        build_lift_basis(d0_sv, word_args, max_target_deg, &one_lit);
    let effective_target = if no_state_args { 0 } else { max_target_deg };

    let mut coeff_names = Vec::new();
    let mut step_arg_templates: Vec<Vec<(String, Vec<(String, PolyExpr)>)>> =
        Vec::with_capacity(skeleton.len());
    let mut c_idx = 0usize;
    let mut skeleton_linear = true;

    for op in skeleton {
        if op
            .domain_laws
            .iter()
            .any(|dl| poly_expr_degree(&dl.polynomial) > 1)
            || op.updates.values().any(|u| poly_expr_degree(u) > 1)
        {
            skeleton_linear = false;
        }
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

    let model_linear = skeleton_linear
        && base_dw_laws.iter().all(|l| poly_expr_degree(l) <= 1)
        && composed_lift.values().all(|e| poly_expr_degree(e) <= 1)
        && skeleton.iter().all(|op| {
            composed_h
                .word_translation
                .for_operation(&op.name)
                .is_some_and(|tw| {
                    tw.steps
                        .iter()
                        .all(|ts| ts.arg_exprs.iter().all(|ae| poly_expr_degree(ae) <= 1))
                })
        });
    let template_is_complete =
        coeff_names.is_empty() || (achieved_deg >= effective_target && model_linear);

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

    let solve = solve_obligations_and_evals(
        &obs,
        &[],
        eval_conds,
        coeff_domain,
        point_domain,
        &lift_param_vars,
    );
    let lift_witness = match solve.verdict {
        Verdict::Undetermined(r) => return Err(r),
        Verdict::Refuted => {
            if template_is_complete {
                return Ok(None);
            }
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "nonlinear_word_lift_template_out_of_scope".to_owned(),
                detail: "word lift may require higher-degree or non-template polynomial arguments outside decidable template".to_owned(),
            });
        }
        Verdict::Established => solve.witness.expect("witness"),
    };

    let build_and_verify = |cand_subst: &BTreeMap<String, PolyExpr>| -> Result<
        Option<(Vec<WordStepExpr>, WordPreservationCheck, Option<String>)>,
        SilenceReason,
    > {
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
                arg_exprs.push(substitute_poly_expr(&raw, &empty, &empty, cand_subst));
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
            eval_conds,
            coeff_domain,
            point_domain,
        )?;
        if check.domain_nonempty && check.state_commutativity_matched && check.observation_preserved
        {
            Ok(Some((candidate_steps, check, None)))
        } else {
            Ok(Some((candidate_steps, check, Some("failed".to_owned()))))
        }
    };

    let make_subst = |raw_subst: &BTreeMap<String, PolyExpr>,
                      assign_map: &BTreeMap<String, PolyExpr>|
     -> BTreeMap<String, PolyExpr> {
        let mut subst = BTreeMap::new();
        for (k, expr) in raw_subst {
            subst.insert(
                k.clone(),
                substitute_poly_expr(expr, &empty, &empty, assign_map),
            );
        }
        for (k, v) in assign_map {
            subst.insert(k.clone(), v.clone());
        }
        subst
    };

    let raw_subst = lift_witness.to_param_subst(&lift_param_vars);
    let unassigned = lift_witness.unassigned_parameters();
    let zero_vars = VarOrder::new(vec![]).map_err(map_algebra_silence)?;

    if !lift_witness.remaining_nonlinear().is_empty() {
        for tuple in grid_candidates(unassigned.len()) {
            let assign_map: BTreeMap<String, PolyExpr> = unassigned
                .iter()
                .zip(&tuple)
                .map(|(n, &v)| (n.clone(), domain_int_lit(coeff_domain, v)))
                .collect();
            let cand_subst = make_subst(&raw_subst, &assign_map);
            let sub_obs: Vec<PreservationObligation> = obs
                .iter()
                .map(|o| PreservationObligation {
                    state_vars: o.state_vars.clone(),
                    arg_vars: o.arg_vars.clone(),
                    source_laws: o
                        .source_laws
                        .iter()
                        .map(|l| substitute_poly_expr(l, &empty, &empty, &cand_subst))
                        .collect(),
                    target: substitute_poly_expr(&o.target, &empty, &empty, &cand_subst),
                })
                .collect();
            let verify = solve_obligations_and_evals(
                &sub_obs,
                &[],
                eval_conds,
                coeff_domain,
                point_domain,
                &zero_vars,
            );
            if verify.verdict == Verdict::Established
                && let Some((steps, check, None)) = build_and_verify(&cand_subst)?
            {
                return Ok(Some((steps, check)));
            }
        }
        return Err(SilenceReason::NonLinearRationalOrIntegerExistence {
            point_domain: point_domain.clone(),
            detail: "old word lift requires solving nonlinear coefficient constraints".to_owned(),
        });
    }

    let candidates = if unassigned.is_empty() {
        vec![BTreeMap::new()]
    } else if unassigned.len() <= 3 {
        grid_candidates(unassigned.len())
            .into_iter()
            .map(|tuple| {
                unassigned
                    .iter()
                    .zip(&tuple)
                    .map(|(n, &v)| (n.clone(), domain_int_lit(coeff_domain, v)))
                    .collect::<BTreeMap<_, _>>()
            })
            .collect()
    } else {
        vec![
            unassigned
                .iter()
                .map(|n| (n.clone(), zero_lit()))
                .collect::<BTreeMap<_, _>>(),
        ]
    };
    let mut last_detail = String::new();
    for assign_map in candidates {
        let cand_subst = make_subst(&raw_subst, &assign_map);
        if let Some((steps, check, err)) = build_and_verify(&cand_subst)? {
            if err.is_none() {
                return Ok(Some((steps, check)));
            }
            last_detail = check.detail;
        }
    }
    if unassigned.is_empty() {
        Ok(None)
    } else {
        Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "lift_candidate_specialization_failed".to_owned(),
            detail: if last_detail.is_empty() {
                "parameterized old word lift specialization failed check".to_owned()
            } else {
                last_detail
            },
        })
    }
}
