//! 許容部分加群 `H` 上のアフィン修復全解（微小・有限変位、体係数および $\mathbb{Z}$ 係数共通）（G-141 E6・H1）。

use crate::algebra::scalar::RingCoeff;
use crate::ir::lift::AffineAllowedSpec;
use crate::ir::result::SilenceReason;
use crate::ir::result_phase4::AffineRepairResult;
use crate::solver::lift::CoreLift;
use crate::solver::lift_backend::{LiftContext, LiftRingBackend};
use crate::solver::lift_common::{
    apply_m_shift, apply_rp_subset_shift, concat_vecs, expand_subset_delta, format_subset_m_map,
    format_subset_rp_map, map_lift_algebra_error, reevaluate_laws_in_rp,
};
use std::collections::BTreeMap;

/// 許容部分加群 `H` アフィン修復全解（G-141 E6・H1）。
pub(crate) fn compute_affine_repair<B: LiftRingBackend>(
    ctx: &LiftContext<'_, B>,
    aff: &AffineAllowedSpec,
    core: &CoreLift<B::Coeff>,
) -> Result<AffineRepairResult, SilenceReason> {
    let var_idx: BTreeMap<&str, usize> = ctx
        .spec
        .variables
        .iter()
        .enumerate()
        .map(|(i, v)| (v.as_str(), i))
        .collect();
    let allowed_indices: Vec<usize> = aff
        .allowed_vars
        .iter()
        .map(|v| var_idx[v.as_str()])
        .collect();

    if aff.finite_displacement {
        return compute_finite_affine_repair(ctx, aff, &allowed_indices);
    }

    let dm = ctx.ext.kernel_dim();
    let z = ctx.backend.zero();
    let num_cols = allowed_indices.len() * dm;
    let num_rows = core.complex.dim1();
    let mut sub_d0 = vec![vec![z.clone(); num_cols]; num_rows];
    for (row, dst_row) in sub_d0.iter_mut().enumerate().take(num_rows) {
        for (c_block, &v_idx) in allowed_indices.iter().enumerate() {
            for k in 0..dm {
                dst_row[c_block * dm + k] = core.complex.d0()[row][v_idx * dm + k].clone();
            }
        }
    }
    let neg_res: Vec<B::Coeff> = core.residual_m.iter().map(RingCoeff::neg_ref).collect();

    match ctx
        .backend
        .solve_affine(&sub_d0, &neg_res, num_cols)
        .map_err(map_lift_algebra_error)?
    {
        Some((particular, kernel_basis)) => {
            let full_delta = expand_subset_delta(
                ctx.spec.variables.len(),
                &allowed_indices,
                dm,
                &particular,
                &z,
            );
            let shifted = apply_m_shift(&ctx.ext, &ctx.ambient_lift_rp, &full_delta)
                .map_err(map_lift_algebra_error)?;
            let mut reeval =
                reevaluate_laws_in_rp(&ctx.law_polys, &shifted, &ctx.param_vals_rp, &ctx.ext)
                    .map_err(map_lift_algebra_error)?;
            let particular_map = format_subset_m_map(&aff.allowed_vars, &particular, &ctx.ext);
            let mut torsor_maps = Vec::with_capacity(kernel_basis.len());
            for kb in &kernel_basis {
                let kb_full =
                    expand_subset_delta(ctx.spec.variables.len(), &allowed_indices, dm, kb, &z);
                let shifted_k =
                    apply_m_shift(&ctx.ext, &shifted, &kb_full).map_err(map_lift_algebra_error)?;
                let re_k =
                    reevaluate_laws_in_rp(&ctx.law_polys, &shifted_k, &ctx.param_vals_rp, &ctx.ext)
                        .map_err(map_lift_algebra_error)?;
                if !re_k.matched {
                    reeval.matched = false;
                }
                torsor_maps.push(format_subset_m_map(&aff.allowed_vars, kb, &ctx.ext));
            }
            Ok(AffineRepairResult {
                finite_displacement: false,
                allowed_vars: aff.allowed_vars.clone(),
                repair_exists: true,
                particular_delta: Some(particular_map),
                torsor_basis: torsor_maps,
                reevaluation: Some(reeval),
            })
        }
        None => Ok(AffineRepairResult {
            finite_displacement: false,
            allowed_vars: aff.allowed_vars.clone(),
            repair_exists: false,
            particular_delta: None,
            torsor_basis: Vec::new(),
            reevaluation: None,
        }),
    }
}

fn compute_finite_affine_repair<B: LiftRingBackend>(
    ctx: &LiftContext<'_, B>,
    aff: &AffineAllowedSpec,
    allowed_indices: &[usize],
) -> Result<AffineRepairResult, SilenceReason> {
    let dp = ctx.ext.r_prime().dim();
    let z = ctx.backend.zero();
    let full_base = concat_vecs(&ctx.ambient_lift_rp, &ctx.param_vals_rp);

    for poly in &ctx.law_polys {
        for mono in poly.terms().keys() {
            let deg_allowed: u32 = allowed_indices.iter().map(|&idx| mono.exps()[idx]).sum();
            if deg_allowed > 1 {
                return Err(SilenceReason::SyzygyOutOfScope {
                    detail:
                        "finite_displacement affine repair requires laws affine in allowed_vars"
                            .to_owned(),
                });
            }
        }
    }

    let num_cols = allowed_indices.len() * dp;
    let num_rows = ctx.law_polys.len() * dp;
    let mut mat = vec![vec![z; num_cols]; num_rows];
    let mut rhs = Vec::with_capacity(num_rows);

    for (i, poly) in ctx.law_polys.iter().enumerate() {
        let res_rp = ctx
            .ext
            .r_prime()
            .eval_poly(poly, &full_base)
            .map_err(map_lift_algebra_error)?;
        rhs.extend(ctx.ext.r_prime().neg(&res_rp));
        for (c_block, &v_idx) in allowed_indices.iter().enumerate() {
            let deriv = poly
                .partial_derivative(v_idx)
                .map_err(map_lift_algebra_error)?;
            let coeff_rp = ctx
                .ext
                .r_prime()
                .eval_poly(&deriv, &full_base)
                .map_err(map_lift_algebra_error)?;
            for col_k in 0..dp {
                let ek = ctx.ext.r_prime().basis_elem(col_k);
                let prod = ctx.ext.r_prime().mul(&coeff_rp, &ek);
                for (row_k, val) in prod.into_iter().enumerate() {
                    mat[i * dp + row_k][c_block * dp + col_k] = val;
                }
            }
        }
    }

    match ctx
        .backend
        .solve_affine(&mat, &rhs, num_cols)
        .map_err(map_lift_algebra_error)?
    {
        Some((particular, kernel_basis)) => {
            let shifted = apply_rp_subset_shift(
                &ctx.ambient_lift_rp,
                allowed_indices,
                dp,
                &particular,
                &ctx.ext,
            );
            let mut reeval =
                reevaluate_laws_in_rp(&ctx.law_polys, &shifted, &ctx.param_vals_rp, &ctx.ext)
                    .map_err(map_lift_algebra_error)?;
            let particular_map = format_subset_rp_map(&aff.allowed_vars, &particular, dp, &ctx.ext);
            let mut torsor_maps = Vec::with_capacity(kernel_basis.len());
            for kb in &kernel_basis {
                let shifted_k = apply_rp_subset_shift(&shifted, allowed_indices, dp, kb, &ctx.ext);
                let re_k =
                    reevaluate_laws_in_rp(&ctx.law_polys, &shifted_k, &ctx.param_vals_rp, &ctx.ext)
                        .map_err(map_lift_algebra_error)?;
                if !re_k.matched {
                    reeval.matched = false;
                }
                torsor_maps.push(format_subset_rp_map(&aff.allowed_vars, kb, dp, &ctx.ext));
            }
            Ok(AffineRepairResult {
                finite_displacement: true,
                allowed_vars: aff.allowed_vars.clone(),
                repair_exists: true,
                particular_delta: Some(particular_map),
                torsor_basis: torsor_maps,
                reevaluation: Some(reeval),
            })
        }
        None => Ok(AffineRepairResult {
            finite_displacement: true,
            allowed_vars: aff.allowed_vars.clone(),
            repair_exists: false,
            particular_delta: None,
            torsor_basis: Vec::new(),
            reevaluation: None,
        }),
    }
}
