//! `solver/lift` の補助解析群（`T_raw` 比較・相対 cone `F_u`・宣言被覆 E7/二文脈 Čech）。

use crate::algebra::cochain::CochainComplex;
use crate::algebra::poly::Poly;
use crate::algebra::poly_expr::ExprBindings;
use crate::algebra::scalar::RingCoeff;
use crate::algebra::syzygy::jacobian_polys;
use crate::ir::lift::{DeclarationCoverSpec, RelativeReadingSpec};
use crate::ir::result::SilenceReason;
use crate::ir::result_phase4::{
    DeclarationCoverResult, RawCechComparisonResult, RelativeConeResult,
};
use crate::ir::term::PolyExpr;
use crate::solver::lift::CoreLift;
use crate::solver::lift_backend::{LiftContext, LiftRingBackend};
use crate::solver::lift_common::{
    apply_m_shift, check_cover_support_closure, concat_vecs, eval_var_coords_generic,
    expand_named_polys, expand_subset_delta, expr_supported_in, format_var_map,
    grad_vanishes_on_basis, map_lift_algebra_error, r_action_matrix, reevaluate_laws_in_rp,
    write_block,
};
use std::collections::{BTreeMap, BTreeSet};

/// 生宣言 Čech total complex `T_raw`（`d^1 = 0`）と全 syzygy 複体 `D` の比較（G-141 E8・H3）。
pub(crate) fn compute_raw_cech<B: LiftRingBackend>(
    backend: &B,
    complex_d: &CochainComplex<B::Coeff>,
    h1_d_dim: usize,
) -> Result<RawCechComparisonResult, SilenceReason> {
    let stats = backend
        .raw_cech_stats(complex_d)
        .map_err(map_lift_algebra_error)?;
    Ok(RawCechComparisonResult {
        h0_t_raw_dim: stats.h0_t_raw_dim,
        h1_t_raw_dim: stats.h1_t_raw_dim,
        h1_d_dim,
        kernel_map_exact_verified: stats.h1_t_raw_dim == h1_d_dim + stats.d1_rank,
        differs_from_full_syzygy: stats.h1_t_raw_dim != h1_d_dim,
    })
}

pub(crate) struct ComputedRelativeCone<C: RingCoeff> {
    pub(crate) result: RelativeConeResult,
    pub(crate) fu: CochainComplex<C>,
    pub(crate) rel_cocycle: Vec<C>,
    pub(crate) raw_val_rp: Option<(Vec<C>, bool)>,
}

/// 相対 cone 複体 `F_u = Cone(φ)[-1]` の計算と raw read 差の符号付き比較（G-141 E5・H4・H10）。
pub(crate) fn compute_relative_cone<B: LiftRingBackend>(
    ctx: &LiftContext<'_, B>,
    rel: &RelativeReadingSpec,
    core: &CoreLift<B::Coeff>,
) -> Result<ComputedRelativeCone<B::Coeff>, SilenceReason> {
    ctx.backend
        .check_obs_laws_supported(!rel.obs_laws.is_empty())?;

    let n = ctx.spec.variables.len();
    let r = ctx.law_polys.len();
    let m = rel.obs_vars.len();
    let dm = ctx.ext.kernel_dim();
    let z = ctx.backend.zero();
    let expand = |e: &_, b: &_| ctx.backend.expand_expr(e, b);

    let rm_map: BTreeMap<&str, &PolyExpr> = rel
        .reading_map
        .iter()
        .map(|(k, v)| (k.as_str(), v))
        .collect();
    let mut reading_polys = Vec::with_capacity(m);
    for ov in &rel.obs_vars {
        reading_polys.push(
            ctx.backend
                .expand_expr(rm_map[ov.as_str()], &ctx.bindings)
                .map_err(map_lift_algebra_error)?,
        );
    }

    let obs_lift_rp = eval_var_coords_generic(&rel.obs_vars, &rel.designated_obs_lift, &expand)
        .map_err(map_lift_algebra_error)?;
    let base_full_r = concat_vecs(&ctx.base_pt_r, &ctx.param_vals_r);
    for (idx, (rp_poly, y_rp)) in reading_polys.iter().zip(&obs_lift_rp).enumerate() {
        let expected_r = ctx
            .ext
            .r_base()
            .eval_poly(rp_poly, &base_full_r)
            .map_err(map_lift_algebra_error)?;
        let actual_r = ctx.ext.project(y_rp);
        if expected_r != actual_r {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "designated_obs_lift_covers_base_reading".to_owned(),
                detail: format!(
                    "designated_obs_lift `{}` projects to {} != {}",
                    rel.obs_vars[idx],
                    ctx.ext.r_base().format_elem(&actual_r),
                    ctx.ext.r_base().format_elem(&expected_r)
                ),
            });
        }
    }

    let param_names: Vec<String> = ctx
        .spec
        .ring_params
        .iter()
        .map(|p| p.name.clone())
        .collect();
    let (_, obs_bindings) = ExprBindings::from_slices(&rel.obs_vars, &[], &param_names)
        .map_err(map_lift_algebra_error)?;
    let obs_law_polys = expand_named_polys(&rel.obs_laws, &obs_bindings, &expand)
        .map_err(map_lift_algebra_error)?;
    let obs_full_rp = concat_vecs(&obs_lift_rp, &ctx.param_vals_rp);
    for (ol, poly) in rel.obs_laws.iter().zip(&obs_law_polys) {
        let v = ctx
            .ext
            .r_prime()
            .eval_poly(poly, &obs_full_rp)
            .map_err(map_lift_algebra_error)?;
        if !ctx.ext.r_prime().is_zero_elem(&v) {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "designated_obs_lift_satisfies_obs_laws".to_owned(),
                detail: format!(
                    "obs_law `{}` is nonzero at designated_obs_lift: {}",
                    ol.name,
                    ctx.ext.r_prime().format_elem(&v)
                ),
            });
        }
    }

    let jac_rho =
        jacobian_polys(&reading_polys, ctx.vars.len()).map_err(map_lift_algebra_error)?;
    let mut j_rho = vec![vec![z.clone(); n * dm]; m * dm];
    for (a, jac_row) in jac_rho.iter().enumerate().take(m) {
        for (j, jac_entry) in jac_row.iter().enumerate().take(n) {
            let val_r = ctx
                .ext
                .r_base()
                .eval_poly(jac_entry, &base_full_r)
                .map_err(map_lift_algebra_error)?;
            let block =
                r_action_matrix(ctx.backend, &ctx.ext, &val_r).map_err(map_lift_algebra_error)?;
            write_block(&mut j_rho, a * dm, j * dm, &block);
        }
    }

    let q_dm = core.complex.dim2();
    let l = obs_law_polys.len();
    let mut d0_fu = vec![vec![z.clone(); n * dm]; (r + m) * dm];
    for (row_idx, row) in core.complex.d0().iter().enumerate() {
        d0_fu[row_idx] = row.clone();
    }
    for (row_idx, row) in j_rho.iter().enumerate() {
        d0_fu[r * dm + row_idx] = row.clone();
    }

    let mut d1_fu = vec![vec![z.clone(); (r + m) * dm]; q_dm + l * dm];
    for (row_idx, row) in core.complex.d1().iter().enumerate() {
        for (col_idx, val) in row.iter().enumerate() {
            d1_fu[row_idx][col_idx] = val.clone();
        }
    }

    if l > 0 {
        let obs_full_r: Vec<Vec<B::Coeff>> = obs_lift_rp
            .iter()
            .map(|v| ctx.ext.project(v))
            .chain(ctx.param_vals_r.iter().cloned())
            .collect();
        let jac_obs = jacobian_polys(&obs_law_polys, rel.obs_vars.len() + param_names.len())
            .map_err(map_lift_algebra_error)?;
        let subst_vec: Vec<Poly<B::Coeff>> = reading_polys
            .iter()
            .cloned()
            .chain((0..param_names.len()).map(|k| Poly::var(ctx.vars.len(), n + k, z.clone())))
            .collect();
        for a in 0..l {
            let pulled = if subst_vec.is_empty() {
                Poly::constant(ctx.vars.len(), obs_law_polys[a].constant_value())
            } else {
                obs_law_polys[a]
                    .substitute(&subst_vec)
                    .map_err(map_lift_algebra_error)?
            };
            let cofactors = match ctx.backend.ideal_membership(
                &pulled,
                &ctx.law_polys,
                &ctx.vars,
                ctx.max_pairs,
            ) {
                Ok(Some(c)) => c,
                Ok(None) => {
                    return Err(SilenceReason::ApplicabilityConditionNotMet {
                        condition: "reading_preserves_obs_laws".to_owned(),
                        detail: "pulled-back polynomial does not lie in ideal".to_owned(),
                    });
                }
                Err(e) => return Err(map_lift_algebra_error(e)),
            };
            for (i, cf) in cofactors.iter().enumerate() {
                let val_r = ctx
                    .ext
                    .r_base()
                    .eval_poly(cf, &base_full_r)
                    .map_err(map_lift_algebra_error)?;
                let block = r_action_matrix(ctx.backend, &ctx.ext, &val_r)
                    .map_err(map_lift_algebra_error)?;
                write_block(&mut d1_fu, q_dm + a * dm, i * dm, &block);
            }
            for (b, jac_entry) in jac_obs[a].iter().enumerate().take(m) {
                let val_r = ctx
                    .ext
                    .r_base()
                    .eval_poly(jac_entry, &obs_full_r)
                    .map_err(map_lift_algebra_error)?;
                let neg_val = ctx.ext.r_base().neg(&val_r);
                let block = r_action_matrix(ctx.backend, &ctx.ext, &neg_val)
                    .map_err(map_lift_algebra_error)?;
                write_block(&mut d1_fu, q_dm + a * dm, r * dm + b * dm, &block);
            }
        }
    }

    let fu = CochainComplex::new(n * dm, (r + m) * dm, q_dm + l * dm, d0_fu, d1_fu, z.clone())
        .map_err(map_lift_algebra_error)?;

    let lift_full_rp = concat_vecs(&ctx.ambient_lift_rp, &ctx.param_vals_rp);
    let mut rel_cocycle = core.residual_m.clone();
    for (rp_poly, y_rp) in reading_polys.iter().zip(&obs_lift_rp) {
        let read_val = ctx
            .ext
            .r_prime()
            .eval_poly(rp_poly, &lift_full_rp)
            .map_err(map_lift_algebra_error)?;
        let diff = ctx.ext.r_prime().sub(&read_val, y_rp);
        rel_cocycle.extend(
            ctx.backend
                .extract_kernel_coords(&ctx.ext, &diff)
                .map_err(map_lift_algebra_error)?,
        );
    }

    let fu_coh = ctx
        .backend
        .cohomology_and_cocycle(&fu, &rel_cocycle)
        .map_err(map_lift_algebra_error)?;
    if !fu_coh.is_cocycle {
        return Err(SilenceReason::SyzygyOutOfScope {
            detail: "relative cone cocycle verification failed".to_owned(),
        });
    }

    let relative_obstruction_is_zero = fu_coh.is_zero_class;
    let relative_obstruction_coords = fu_coh.class_coords;

    let (restored_relative_lift, reevaluation, restored_shifted) =
        if let Some(witness_pos) = fu_coh.coboundary_witness {
            let delta: Vec<B::Coeff> = witness_pos.iter().map(RingCoeff::neg_ref).collect();
            let shifted = apply_m_shift(&ctx.ext, &ctx.ambient_lift_rp, &delta)
                .map_err(map_lift_algebra_error)?;
            let mut reeval =
                reevaluate_laws_in_rp(&ctx.law_polys, &shifted, &ctx.param_vals_rp, &ctx.ext)
                    .map_err(map_lift_algebra_error)?;
            let shifted_full = concat_vecs(&shifted, &ctx.param_vals_rp);
            let mut obs_bad = Vec::new();
            for (idx, (rp_poly, y_rp)) in reading_polys.iter().zip(&obs_lift_rp).enumerate() {
                let got = ctx
                    .ext
                    .r_prime()
                    .eval_poly(rp_poly, &shifted_full)
                    .map_err(map_lift_algebra_error)?;
                if got != *y_rp {
                    obs_bad.push(format!(
                        "{}={} (expected {})",
                        rel.obs_vars[idx],
                        ctx.ext.r_prime().format_elem(&got),
                        ctx.ext.r_prime().format_elem(y_rp)
                    ));
                }
            }
            if !obs_bad.is_empty() {
                reeval.matched = false;
                reeval.detail = format!("{}; obs mismatch: {}", reeval.detail, obs_bad.join(", "));
            } else {
                reeval.detail = format!("{}; designated obs lift matched", reeval.detail);
            }
            let fmt = format_var_map(&ctx.spec.variables, &shifted, ctx.ext.r_prime());
            (Some(fmt), Some(reeval), Some(shifted))
        } else {
            (None, None, None)
        };

    let (raw_read_diff_value, raw_read_diff_signed_match, raw_val_rp) =
        if let Some(rr) = &rel.raw_read_diff {
            let rr_poly = ctx
                .backend
                .expand_expr(&rr.expr, &ctx.bindings)
                .map_err(map_lift_algebra_error)?;
            let mut grad_rr = vec![vec![z.clone(); n * dm]; dm];
            for j in 0..n {
                let dp = rr_poly
                    .partial_derivative(j)
                    .map_err(map_lift_algebra_error)?;
                let val_r = ctx
                    .ext
                    .r_base()
                    .eval_poly(&dp, &base_full_r)
                    .map_err(map_lift_algebra_error)?;
                let blk = r_action_matrix(ctx.backend, &ctx.ext, &val_r)
                    .map_err(map_lift_algebra_error)?;
                write_block(&mut grad_rr, 0, j * dm, &blk);
            }
            if relative_obstruction_is_zero {
                if let Some(shifted) = &restored_shifted {
                    if grad_vanishes_on_basis(&grad_rr, &fu_coh.h0_basis, &z) {
                        let eval_full = concat_vecs(shifted, &ctx.param_vals_rp);
                        let raw_val = ctx
                            .ext
                            .r_prime()
                            .eval_poly(&rr_poly, &eval_full)
                            .map_err(map_lift_algebra_error)?;
                        let matched = Some(ctx.ext.r_prime().is_zero_elem(&raw_val));
                        let formatted = ctx.ext.r_prime().format_elem(&raw_val);
                        (Some(formatted), matched, Some((raw_val, rr.negated)))
                    } else {
                        (None, None, None)
                    }
                } else {
                    (None, None, None)
                }
            } else if let Some((eval_base, ker_j_rho)) =
                align_ambient_to_obs(ctx, &j_rho, &reading_polys, &obs_lift_rp)
            {
                if grad_vanishes_on_basis(&grad_rr, &ker_j_rho, &z) {
                    let eval_full = concat_vecs(&eval_base, &ctx.param_vals_rp);
                    let raw_val = ctx
                        .ext
                        .r_prime()
                        .eval_poly(&rr_poly, &eval_full)
                        .map_err(map_lift_algebra_error)?;
                    let formatted = ctx.ext.r_prime().format_elem(&raw_val);
                    (Some(formatted), None, Some((raw_val, rr.negated)))
                } else {
                    (None, None, None)
                }
            } else {
                (None, None, None)
            }
        } else {
            (None, None, None)
        };

    Ok(ComputedRelativeCone {
        result: RelativeConeResult {
            h0_fu_dim: fu_coh.h0_dim,
            h1_fu_dim: fu_coh.h1_dim,
            relative_obstruction_coords,
            relative_obstruction_is_zero,
            relative_lift_exists: relative_obstruction_is_zero,
            restored_relative_lift,
            reevaluation,
            raw_read_diff_value,
            raw_read_diff_signed_match,
        },
        fu,
        rel_cocycle,
        raw_val_rp,
    })
}

/// 宣言被覆支持閉包（G-141 E7）と二文脈共有演算 Čech 差（G-141 F5・H4・H10）。
pub(crate) fn compute_declaration_cover<B: LiftRingBackend>(
    ctx: &LiftContext<'_, B>,
    cov: &DeclarationCoverSpec,
    core: &CoreLift<B::Coeff>,
    rel_cone: Option<&mut ComputedRelativeCone<B::Coeff>>,
) -> Result<DeclarationCoverResult, SilenceReason> {
    let (support_closed, unclosed_observations) = check_cover_support_closure(
        cov,
        &ctx.spec.variables,
        &ctx.spec.laws,
        ctx.spec.relative_reading.as_ref(),
    );
    let Some(cech) = &cov.two_context_cech else {
        return Ok(DeclarationCoverResult {
            support_closed,
            unclosed_observations,
            two_context_cech_diff: None,
            matches_relative_obstruction: None,
        });
    };
    if !support_closed {
        return Ok(DeclarationCoverResult {
            support_closed: false,
            unclosed_observations,
            two_context_cech_diff: None,
            matches_relative_obstruction: None,
        });
    }

    let left_ctx = cov
        .contexts
        .iter()
        .find(|c| c.name == cech.left_context)
        .ok_or_else(|| SilenceReason::ApplicabilityConditionNotMet {
            condition: "two_context_cech_left".to_owned(),
            detail: format!("missing left context `{}`", cech.left_context),
        })?;
    let right_ctx = cov
        .contexts
        .iter()
        .find(|c| c.name == cech.right_context)
        .ok_or_else(|| SilenceReason::ApplicabilityConditionNotMet {
            condition: "two_context_cech_right".to_owned(),
            detail: format!("missing right context `{}`", cech.right_context),
        })?;

    let (p_l, k_l) = solve_context_local_lift(ctx, &left_ctx.vars, &left_ctx.laws)?;
    let (p_r, k_r) = solve_context_local_lift(ctx, &right_ctx.vars, &right_ctx.laws)?;

    let var_idx: BTreeMap<&str, usize> = ctx
        .spec
        .variables
        .iter()
        .enumerate()
        .map(|(i, v)| (v.as_str(), i))
        .collect();
    let left_vars: BTreeSet<&str> = left_ctx.vars.iter().map(String::as_str).collect();
    let right_vars: BTreeSet<&str> = right_ctx.vars.iter().map(String::as_str).collect();
    let overlap_indices: Vec<usize> = ctx
        .spec
        .variables
        .iter()
        .enumerate()
        .filter(|(_, v)| left_vars.contains(v.as_str()) && right_vars.contains(v.as_str()))
        .map(|(i, _)| i)
        .collect();
    let shared_indices: Vec<usize> = cech
        .shared_vars
        .iter()
        .map(|sv| var_idx[sv.as_str()])
        .collect();
    let dm = ctx.ext.kernel_dim();
    let z = ctx.backend.zero();
    let mut rhs_o = Vec::with_capacity(overlap_indices.len() * dm);
    for &idx in &overlap_indices {
        for k in 0..dm {
            rhs_o.push(p_r[idx * dm + k].sub_ref(&p_l[idx * dm + k]));
        }
    }
    let total_k = k_l.len() + k_r.len();
    let mut cob_mat = vec![vec![z.clone(); total_k]; rhs_o.len()];
    for (c_idx, kb) in k_l.iter().enumerate() {
        for (o_pos, &v_idx) in overlap_indices.iter().enumerate() {
            for k in 0..dm {
                cob_mat[o_pos * dm + k][c_idx] = kb[v_idx * dm + k].clone();
            }
        }
    }
    for (c_off, kb) in k_r.iter().enumerate() {
        let c_idx = k_l.len() + c_off;
        for (o_pos, &v_idx) in overlap_indices.iter().enumerate() {
            for k in 0..dm {
                cob_mat[o_pos * dm + k][c_idx] = kb[v_idx * dm + k].neg_ref();
            }
        }
    }
    let (cech_class_nonzero, left_delta, right_delta) = if total_k == 0 {
        let nonzero = rhs_o.iter().any(|v| !v.coeff_is_zero());
        (nonzero, p_l, p_r)
    } else {
        match ctx
            .backend
            .solve_affine(&cob_mat, &rhs_o, total_k)
            .map_err(map_lift_algebra_error)?
        {
            Some((particular, _)) => {
                let mut adj_l = p_l;
                for (c, kb) in particular[..k_l.len()].iter().zip(&k_l) {
                    if !c.coeff_is_zero() {
                        for (dst, src) in adj_l.iter_mut().zip(kb) {
                            *dst = dst.add_ref(&c.mul_ref(src));
                        }
                    }
                }
                let mut adj_r = p_r;
                for (c, kb) in particular[k_l.len()..].iter().zip(&k_r) {
                    if !c.coeff_is_zero() {
                        for (dst, src) in adj_r.iter_mut().zip(kb) {
                            *dst = dst.add_ref(&c.mul_ref(src));
                        }
                    }
                }
                (false, adj_l, adj_r)
            }
            None => (true, p_l, p_r),
        }
    };

    let left_lift = apply_m_shift(&ctx.ext, &ctx.ambient_lift_rp, &left_delta)
        .map_err(map_lift_algebra_error)?;
    let right_lift = apply_m_shift(&ctx.ext, &ctx.ambient_lift_rp, &right_delta)
        .map_err(map_lift_algebra_error)?;

    let mut diff_map = BTreeMap::new();
    for (sv, &idx) in cech.shared_vars.iter().zip(&shared_indices) {
        let d = ctx.ext.r_prime().sub(&right_lift[idx], &left_lift[idx]);
        diff_map.insert(sv.clone(), ctx.ext.r_prime().format_elem(&d));
    }

    let matches_relative_obstruction = if let Some(rc) = rel_cone {
        let left_laws: BTreeSet<&str> = left_ctx.laws.iter().map(String::as_str).collect();
        let mut overlap_diff = vec![z.clone(); ctx.spec.variables.len() * dm];
        for &j in &overlap_indices {
            for k in 0..dm {
                overlap_diff[j * dm + k] = right_delta[j * dm + k].sub_ref(&left_delta[j * dm + k]);
            }
        }
        let mut mv_cocycle = vec![z.clone(); rc.fu.dim1()];
        for (i, law) in ctx.spec.laws.iter().enumerate() {
            if left_laws.contains(law.name.as_str()) {
                for row_k in 0..dm {
                    let row = &core.complex.d0()[i * dm + row_k];
                    let mut acc = z.clone();
                    for (a, b) in row.iter().zip(&overlap_diff) {
                        if !a.coeff_is_zero() && !b.coeff_is_zero() {
                            acc = acc.add_ref(&a.mul_ref(b));
                        }
                    }
                    mv_cocycle[i * dm + row_k] = acc;
                }
            }
        }
        if let Some(rel) = &ctx.spec.relative_reading {
            let rm_map: BTreeMap<&str, &PolyExpr> = rel
                .reading_map
                .iter()
                .map(|(k, v)| (k.as_str(), v))
                .collect();
            let r_offset = ctx.spec.laws.len() * dm;
            for (a, ov) in rel.obs_vars.iter().enumerate() {
                if expr_supported_in(rm_map[ov.as_str()], &left_vars) {
                    for row_k in 0..dm {
                        let row = &rc.fu.d0()[r_offset + a * dm + row_k];
                        let mut acc = z.clone();
                        for (c_val, b) in row.iter().zip(&overlap_diff) {
                            if !c_val.coeff_is_zero() && !b.coeff_is_zero() {
                                acc = acc.add_ref(&c_val.mul_ref(b));
                            }
                        }
                        mv_cocycle[r_offset + a * dm + row_k] = acc;
                    }
                }
            }
        }
        let mv_is_cocycle = rc.fu.d1().iter().all(|row| {
            let mut acc = z.clone();
            for (a, b) in row.iter().zip(&mv_cocycle) {
                if !a.coeff_is_zero() && !b.coeff_is_zero() {
                    acc = acc.add_ref(&a.mul_ref(b));
                }
            }
            acc.coeff_is_zero()
        });
        let class_diff: Vec<B::Coeff> = rc
            .rel_cocycle
            .iter()
            .zip(&mv_cocycle)
            .map(|(a, b)| a.sub_ref(b))
            .collect();
        let class_matches = mv_is_cocycle
            && matches!(
                ctx.backend
                    .solve_affine(rc.fu.d0(), &class_diff, rc.fu.dim0()),
                Ok(Some(_))
            );

        if let Some((raw_val, negated)) = &rc.raw_val_rp
            && !rc.result.relative_obstruction_is_zero
            && shared_indices.len() == 1
        {
            let target_rp = if *negated {
                ctx.ext.r_prime().neg(raw_val)
            } else {
                raw_val.clone()
            };
            let oriented_match = match ctx.backend.extract_kernel_coords(&ctx.ext, &target_rp) {
                Ok(target_m) => {
                    let target_var_idx = shared_indices[0];
                    let mut target_overlap = vec![z.clone(); rhs_o.len()];
                    if let Some(o_pos) = overlap_indices.iter().position(|&v| v == target_var_idx) {
                        for k in 0..dm {
                            target_overlap[o_pos * dm + k] = target_m[k].clone();
                        }
                    }
                    let residual: Vec<B::Coeff> = rhs_o
                        .iter()
                        .zip(&target_overlap)
                        .map(|(a, b)| a.sub_ref(b))
                        .collect();
                    if total_k == 0 {
                        residual.iter().all(RingCoeff::coeff_is_zero)
                    } else {
                        matches!(
                            ctx.backend.solve_affine(&cob_mat, &residual, total_k),
                            Ok(Some(_))
                        )
                    }
                }
                Err(_) => false,
            };
            rc.result.raw_read_diff_signed_match = Some(oriented_match);
        }

        Some(class_matches && (rc.result.relative_obstruction_is_zero != cech_class_nonzero))
    } else {
        None
    };

    Ok(DeclarationCoverResult {
        support_closed,
        unclosed_observations,
        two_context_cech_diff: Some(diff_map),
        matches_relative_obstruction,
    })
}

#[allow(clippy::type_complexity)]
fn solve_context_local_lift<B: LiftRingBackend>(
    ctx: &LiftContext<'_, B>,
    ctx_var_names: &[String],
    ctx_law_names: &[String],
) -> Result<(Vec<B::Coeff>, Vec<Vec<B::Coeff>>), SilenceReason> {
    let n = ctx.spec.variables.len();
    let dm = ctx.ext.kernel_dim();
    let z = ctx.backend.zero();
    let expand = |e: &_, b: &_| ctx.backend.expand_expr(e, b);
    let ctx_var_set: BTreeSet<&str> = ctx_var_names.iter().map(String::as_str).collect();
    let ctx_var_indices: Vec<usize> = ctx
        .spec
        .variables
        .iter()
        .enumerate()
        .filter(|(_, v)| ctx_var_set.contains(v.as_str()))
        .map(|(i, _)| i)
        .collect();
    let num_cols = ctx_var_indices.len() * dm;
    let law_set: BTreeSet<&str> = ctx_law_names.iter().map(String::as_str).collect();
    let active_laws: Vec<&Poly<B::Coeff>> = ctx
        .spec
        .laws
        .iter()
        .zip(&ctx.law_polys)
        .filter(|(l, _)| law_set.contains(l.name.as_str()))
        .map(|(_, p)| p)
        .collect();

    let base_full_r = concat_vecs(&ctx.base_pt_r, &ctx.param_vals_r);
    let lift_full_rp = concat_vecs(&ctx.ambient_lift_rp, &ctx.param_vals_rp);

    let mut rows = Vec::new();
    let mut rhs = Vec::new();
    for poly in &active_laws {
        let val_rp = ctx
            .ext
            .r_prime()
            .eval_poly(poly, &lift_full_rp)
            .map_err(map_lift_algebra_error)?;
        let res_m = ctx
            .backend
            .extract_kernel_coords(&ctx.ext, &val_rp)
            .map_err(map_lift_algebra_error)?;
        let mut row_block = vec![vec![z.clone(); num_cols]; dm];
        for (c_pos, &j) in ctx_var_indices.iter().enumerate() {
            let dp = poly.partial_derivative(j).map_err(map_lift_algebra_error)?;
            let val_r = ctx
                .ext
                .r_base()
                .eval_poly(&dp, &base_full_r)
                .map_err(map_lift_algebra_error)?;
            let blk =
                r_action_matrix(ctx.backend, &ctx.ext, &val_r).map_err(map_lift_algebra_error)?;
            write_block(&mut row_block, 0, c_pos * dm, &blk);
        }
        rows.extend(row_block);
        rhs.extend(res_m.into_iter().map(|v| v.neg_ref()));
    }

    if let Some(rel) = &ctx.spec.relative_reading {
        let obs_lift_rp =
            eval_var_coords_generic(&rel.obs_vars, &rel.designated_obs_lift, &expand)
                .map_err(map_lift_algebra_error)?;
        let rm_map: BTreeMap<&str, &PolyExpr> = rel
            .reading_map
            .iter()
            .map(|(k, v)| (k.as_str(), v))
            .collect();
        for (ov, y_rp) in rel.obs_vars.iter().zip(&obs_lift_rp) {
            let expr = rm_map[ov.as_str()];
            if !expr_supported_in(expr, &ctx_var_set) {
                continue;
            }
            let rp_poly = ctx
                .backend
                .expand_expr(expr, &ctx.bindings)
                .map_err(map_lift_algebra_error)?;
            let read_val = ctx
                .ext
                .r_prime()
                .eval_poly(&rp_poly, &lift_full_rp)
                .map_err(map_lift_algebra_error)?;
            let diff = ctx.ext.r_prime().sub(&read_val, y_rp);
            let w_m = ctx
                .backend
                .extract_kernel_coords(&ctx.ext, &diff)
                .map_err(map_lift_algebra_error)?;
            let mut row_block = vec![vec![z.clone(); num_cols]; dm];
            for (c_pos, &j) in ctx_var_indices.iter().enumerate() {
                let dp = rp_poly
                    .partial_derivative(j)
                    .map_err(map_lift_algebra_error)?;
                let val_r = ctx
                    .ext
                    .r_base()
                    .eval_poly(&dp, &base_full_r)
                    .map_err(map_lift_algebra_error)?;
                let blk = r_action_matrix(ctx.backend, &ctx.ext, &val_r)
                    .map_err(map_lift_algebra_error)?;
                write_block(&mut row_block, 0, c_pos * dm, &blk);
            }
            rows.extend(row_block);
            rhs.extend(w_m.into_iter().map(|v| v.neg_ref()));
        }
    }

    match ctx
        .backend
        .solve_affine(&rows, &rhs, num_cols)
        .map_err(map_lift_algebra_error)?
    {
        Some((particular, kernel_basis)) => {
            let full_p = expand_subset_delta(n, &ctx_var_indices, dm, &particular, &z);
            let full_k = kernel_basis
                .iter()
                .map(|kb| expand_subset_delta(n, &ctx_var_indices, dm, kb, &z))
                .collect();
            Ok((full_p, full_k))
        }
        None => Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "two_context_local_lift_exists".to_owned(),
            detail: "local lift does not exist on one of the two contexts".to_owned(),
        }),
    }
}

#[allow(clippy::type_complexity)]
fn align_ambient_to_obs<B: LiftRingBackend>(
    ctx: &LiftContext<'_, B>,
    j_rho: &[Vec<B::Coeff>],
    reading_polys: &[Poly<B::Coeff>],
    obs_lift_rp: &[Vec<B::Coeff>],
) -> Option<(Vec<Vec<B::Coeff>>, Vec<Vec<B::Coeff>>)> {
    let full = concat_vecs(&ctx.ambient_lift_rp, &ctx.param_vals_rp);
    let mut neg_w = Vec::new();
    for (rp_poly, y_rp) in reading_polys.iter().zip(obs_lift_rp) {
        let got = ctx.ext.r_prime().eval_poly(rp_poly, &full).ok()?;
        let diff = ctx.ext.r_prime().sub(y_rp, &got);
        neg_w.extend(ctx.backend.extract_kernel_coords(&ctx.ext, &diff).ok()?);
    }
    let num_cols = ctx.ambient_lift_rp.len() * ctx.ext.kernel_dim();
    match ctx.backend.solve_affine(j_rho, &neg_w, num_cols).ok()? {
        Some((particular, kernel_basis)) => Some((
            apply_m_shift(&ctx.ext, &ctx.ambient_lift_rp, &particular).ok()?,
            kernel_basis,
        )),
        None => None,
    }
}
