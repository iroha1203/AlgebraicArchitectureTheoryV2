//! 原子操作 adapter の一般拡張操作言語非移送検査（G-141 H12）。
//!
//! 原子操作の可換性 `g ∘ op_before == op_after ∘ g` を一般多項式恒等式で検算し、
//! 拡張プロトコル語（`ProtocolSequence`）および状態依存実行時引数操作（`RuntimeArgOp`）の
//! 移送成否と中間状態 Law 残差を一般構成から導出する。

use crate::algebra::MonomialOrder;
use crate::algebra::poly::{AlgebraError, Poly};
use crate::algebra::poly_expr::{ExprBindings, VarOrder};
use crate::algebra::scalar::RingCoeff;
use crate::ir::atlas::{ExtendedLanguageCheckSpec, ExtendedOperationCheckSpec};
use crate::ir::result::SilenceReason;
use crate::ir::result_phase4::{ExtendedCheckOutcome, ExtendedLanguageResult};
use crate::ir::term::PolyExpr;
use crate::solver::atlas::{eval_const_expr, map_atlas_alg_err};
use std::collections::BTreeMap;

/// `ExtendedLanguageCheckSpec` の原子操作可換性および拡張操作チェックをすべて評価する。
pub(crate) fn compute_extended_language_check<C, FE>(
    ext: &ExtendedLanguageCheckSpec,
    zero: C,
    expand: &FE,
) -> Result<ExtendedLanguageResult, SilenceReason>
where
    C: RingCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
{
    let (_, empty_bindings) = ExprBindings::from_slices(&[], &[], &[]).map_err(map_atlas_alg_err)?;
    let (state_order, state_bindings) =
        ExprBindings::from_slices(&ext.state_vars, &[], &[]).map_err(map_atlas_alg_err)?;

    // adapter g: R^n -> R^n を状態変数多項式として展開。
    let adapter_map_by_var: BTreeMap<&str, &PolyExpr> = ext
        .adapter_map
        .iter()
        .map(|(v, e)| (v.as_str(), e))
        .collect();
    let mut adapter_state_polys = Vec::with_capacity(ext.state_vars.len());
    for v in &ext.state_vars {
        adapter_state_polys.push(
            expand(adapter_map_by_var[v.as_str()], &state_bindings).map_err(map_atlas_alg_err)?,
        );
    }

    // 1. 原子操作の多項式恒等式可換性検査: g(op_before(x, args)) == op_after(g(x), args)
    let mut atomic_ops_commute = BTreeMap::new();
    for op in &ext.atomic_ops {
        let (_, op_bindings) = ExprBindings::from_slices(&ext.state_vars, &op.arg_vars, &[])
            .map_err(map_atlas_alg_err)?;
        let n_state = ext.state_vars.len();
        let n_args = op.arg_vars.len();
        let total_vars = n_state + n_args;

        let g_polys: Vec<Poly<C>> = ext
            .state_vars
            .iter()
            .map(|v| expand(adapter_map_by_var[v.as_str()], &op_bindings))
            .collect::<Result<_, _>>()
            .map_err(map_atlas_alg_err)?;

        let before_by_var: BTreeMap<&str, &PolyExpr> = op
            .before_updates
            .iter()
            .map(|(v, e)| (v.as_str(), e))
            .collect();
        let after_by_var: BTreeMap<&str, &PolyExpr> = op
            .after_updates
            .iter()
            .map(|(v, e)| (v.as_str(), e))
            .collect();

        let before_polys: Vec<Poly<C>> = ext
            .state_vars
            .iter()
            .map(|v| expand(before_by_var[v.as_str()], &op_bindings))
            .collect::<Result<_, _>>()
            .map_err(map_atlas_alg_err)?;
        let after_polys: Vec<Poly<C>> = ext
            .state_vars
            .iter()
            .map(|v| expand(after_by_var[v.as_str()], &op_bindings))
            .collect::<Result<_, _>>()
            .map_err(map_atlas_alg_err)?;

        // 代入ベクトル: (state_updates..., arg_0, ..., arg_{k-1})
        let mut before_subst = before_polys;
        let mut g_subst = g_polys.clone();
        for a_idx in 0..n_args {
            let arg_var = Poly::var(total_vars, n_state + a_idx, zero.zero_like());
            before_subst.push(arg_var.clone());
            g_subst.push(arg_var);
        }

        let mut commutes = true;
        for coord in 0..n_state {
            let lhs = g_polys[coord]
                .substitute(&before_subst)
                .map_err(map_atlas_alg_err)?;
            let rhs = after_polys[coord]
                .substitute(&g_subst)
                .map_err(map_atlas_alg_err)?;
            if lhs != rhs {
                commutes = false;
                break;
            }
        }
        atomic_ops_commute.insert(op.name.clone(), commutes);
    }
    let all_atomic_ops_commute = atomic_ops_commute.values().all(|&b| b);

    // 2. 拡張操作・プロトコル語の移送検査。
    let mut extended_check_results = Vec::with_capacity(ext.extended_checks.len());
    for chk in &ext.extended_checks {
        match chk {
            ExtendedOperationCheckSpec::ProtocolSequence {
                name,
                extended_state_vars,
                initial_state,
                before_steps,
                after_steps,
                before_read,
                after_read,
                intermediate_laws,
            } => {
                let res = eval_protocol_sequence(
                    name,
                    extended_state_vars,
                    initial_state,
                    before_steps,
                    after_steps,
                    before_read,
                    after_read,
                    intermediate_laws,
                    &empty_bindings,
                    expand,
                )?;
                extended_check_results.push(res);
            }
            ExtendedOperationCheckSpec::RuntimeArgOp {
                name,
                before_updates,
                after_updates,
                sample_state,
            } => {
                let res = eval_runtime_arg_op(
                    name,
                    &ext.state_vars,
                    &state_order,
                    &adapter_state_polys,
                    before_updates,
                    after_updates,
                    sample_state,
                    &state_bindings,
                    &empty_bindings,
                    expand,
                )?;
                extended_check_results.push(res);
            }
        }
    }
    let all_extended_checks_preserved = extended_check_results
        .iter()
        .all(|c| c.transport_preserved);

    Ok(ExtendedLanguageResult {
        atomic_ops_commute,
        all_atomic_ops_commute,
        extended_check_results,
        all_extended_checks_preserved,
    })
}

#[allow(clippy::too_many_arguments)]
fn eval_protocol_sequence<C, FE>(
    name: &str,
    extended_state_vars: &[String],
    initial_state: &[(String, PolyExpr)],
    before_steps: &[Vec<(String, PolyExpr)>],
    after_steps: &[Vec<(String, PolyExpr)>],
    before_read: &PolyExpr,
    after_read: &PolyExpr,
    intermediate_laws: &[crate::ir::change::NamedPoly],
    empty_bindings: &ExprBindings,
    expand: &FE,
) -> Result<ExtendedCheckOutcome, SilenceReason>
where
    C: RingCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
{
    let (_, ext_bindings) =
        ExprBindings::from_slices(extended_state_vars, &[], &[]).map_err(map_atlas_alg_err)?;

    let init_map: BTreeMap<&str, &PolyExpr> =
        initial_state.iter().map(|(v, e)| (v.as_str(), e)).collect();
    let mut init_vec = Vec::with_capacity(extended_state_vars.len());
    for v in extended_state_vars {
        init_vec.push(eval_const_expr(init_map[v.as_str()], empty_bindings, expand)?);
    }

    let law_polys: Vec<(&str, Poly<C>)> = intermediate_laws
        .iter()
        .map(|l| Ok((l.name.as_str(), expand(&l.expr, &ext_bindings)?)))
        .collect::<Result<_, AlgebraError>>()
        .map_err(map_atlas_alg_err)?;

    let run_steps = |steps: &[Vec<(String, PolyExpr)>],
                     record_laws: bool|
     -> Result<(Vec<C>, Vec<String>, bool), SilenceReason> {
        let mut cur = init_vec.clone();
        let mut residuals = Vec::new();
        let mut all_laws_zero = true;
        for (step_idx, step) in steps.iter().enumerate() {
            let smap: BTreeMap<&str, &PolyExpr> =
                step.iter().map(|(v, e)| (v.as_str(), e)).collect();
            let mut next = Vec::with_capacity(extended_state_vars.len());
            for v in extended_state_vars {
                let p = expand(smap[v.as_str()], &ext_bindings).map_err(map_atlas_alg_err)?;
                next.push(p.eval_at(&cur).map_err(map_atlas_alg_err)?);
            }
            cur = next;
            if record_laws {
                for (lname, lpoly) in &law_polys {
                    let rv = lpoly.eval_at(&cur).map_err(map_atlas_alg_err)?;
                    if !rv.coeff_is_zero() {
                        all_laws_zero = false;
                        residuals.push(format!("step{step_idx}:{lname}={rv}"));
                    }
                }
            }
        }
        Ok((cur, residuals, all_laws_zero))
    };

    let (before_final, before_residuals, before_laws_zero) = run_steps(before_steps, true)?;
    let (after_final, mut law_residuals, after_laws_zero) = run_steps(after_steps, true)?;
    if !before_laws_zero {
        for r in before_residuals {
            law_residuals.push(format!("before_{r}"));
        }
    }

    let before_read_val = expand(before_read, &ext_bindings)
        .map_err(map_atlas_alg_err)?
        .eval_at(&before_final)
        .map_err(map_atlas_alg_err)?;
    let after_read_val = expand(after_read, &ext_bindings)
        .map_err(map_atlas_alg_err)?
        .eval_at(&after_final)
        .map_err(map_atlas_alg_err)?;

    let reads_match = before_read_val == after_read_val;
    let transport_preserved = reads_match && before_laws_zero && after_laws_zero;

    Ok(ExtendedCheckOutcome {
        name: name.to_owned(),
        kind: "protocol_sequence".to_owned(),
        transport_preserved,
        before_values: vec![before_read_val.to_string()],
        after_values: vec![after_read_val.to_string()],
        law_residuals,
        detail: format!(
            "on initial_state: before_read={before_read_val}, after_read={after_read_val}, before_laws_satisfied={before_laws_zero}, after_laws_satisfied={after_laws_zero}"
        ),
    })
}

#[allow(clippy::too_many_arguments)]
fn eval_runtime_arg_op<C, FE>(
    name: &str,
    state_vars: &[String],
    state_order: &VarOrder,
    adapter_polys: &[Poly<C>],
    before_updates: &[(String, PolyExpr)],
    after_updates: &[(String, PolyExpr)],
    sample_state: &[(String, PolyExpr)],
    state_bindings: &ExprBindings,
    empty_bindings: &ExprBindings,
    expand: &FE,
) -> Result<ExtendedCheckOutcome, SilenceReason>
where
    C: RingCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
{
    let sample_map: BTreeMap<&str, &PolyExpr> =
        sample_state.iter().map(|(v, e)| (v.as_str(), e)).collect();
    let mut x = Vec::with_capacity(state_vars.len());
    for v in state_vars {
        x.push(eval_const_expr(sample_map[v.as_str()], empty_bindings, expand)?);
    }

    let before_map: BTreeMap<&str, &PolyExpr> = before_updates
        .iter()
        .map(|(v, e)| (v.as_str(), e))
        .collect();
    let after_map: BTreeMap<&str, &PolyExpr> =
        after_updates.iter().map(|(v, e)| (v.as_str(), e)).collect();

    let mut before_polys = Vec::with_capacity(state_vars.len());
    let mut after_polys = Vec::with_capacity(state_vars.len());
    for v in state_vars {
        before_polys.push(expand(before_map[v.as_str()], state_bindings).map_err(map_atlas_alg_err)?);
        after_polys.push(expand(after_map[v.as_str()], state_bindings).map_err(map_atlas_alg_err)?);
    }

    // 1. 多項式恒等式による全域可換性判定: g(op_before(x)) == op_after(g(x))（単一サンプル点偽陽性を排除）。
    let mut poly_identity_holds = true;
    let mut poly_residuals = Vec::new();
    for (coord, v) in state_vars.iter().enumerate() {
        let lhs_poly = adapter_polys[coord]
            .substitute(&before_polys)
            .map_err(map_atlas_alg_err)?;
        let rhs_poly = after_polys[coord]
            .substitute(adapter_polys)
            .map_err(map_atlas_alg_err)?;
        if lhs_poly != rhs_poly {
            poly_identity_holds = false;
            let diff = lhs_poly.sub(&rhs_poly);
            poly_residuals.push(format!(
                "{v}_poly:{}",
                diff.display(state_order, MonomialOrder::Grevlex)
            ));
        }
    }

    // 2. サンプル点での具体評価（witness 出力）。
    let mut op_b_x = Vec::with_capacity(state_vars.len());
    for bp in &before_polys {
        op_b_x.push(bp.eval_at(&x).map_err(map_atlas_alg_err)?);
    }
    let mut lhs = Vec::with_capacity(state_vars.len());
    for gp in adapter_polys {
        lhs.push(gp.eval_at(&op_b_x).map_err(map_atlas_alg_err)?);
    }
    let mut g_x = Vec::with_capacity(state_vars.len());
    for gp in adapter_polys {
        g_x.push(gp.eval_at(&x).map_err(map_atlas_alg_err)?);
    }
    let mut rhs = Vec::with_capacity(state_vars.len());
    for ap in &after_polys {
        rhs.push(ap.eval_at(&g_x).map_err(map_atlas_alg_err)?);
    }

    let sample_matches = lhs == rhs;
    let mut law_residuals: Vec<String> = lhs
        .iter()
        .zip(&rhs)
        .zip(state_vars)
        .filter_map(|((l, r), v)| {
            let diff = l.sub_ref(r);
            if diff.coeff_is_zero() {
                None
            } else {
                Some(format!("{v}:{diff}"))
            }
        })
        .collect();
    if !poly_identity_holds && law_residuals.is_empty() {
        law_residuals = poly_residuals;
    }

    Ok(ExtendedCheckOutcome {
        name: name.to_owned(),
        kind: "runtime_arg_op".to_owned(),
        transport_preserved: poly_identity_holds,
        before_values: lhs.iter().map(ToString::to_string).collect(),
        after_values: rhs.iter().map(ToString::to_string).collect(),
        law_residuals,
        detail: if poly_identity_holds {
            "g(op_before(x)) == op_after(g(x)) holds identically".to_owned()
        } else if sample_matches {
            "g(op_before(x)) != op_after(g(x)) as polynomial maps (equalizer sample point coincided)".to_owned()
        } else {
            "g(op_before(x)) != op_after(g(x))".to_owned()
        },
    })
}
