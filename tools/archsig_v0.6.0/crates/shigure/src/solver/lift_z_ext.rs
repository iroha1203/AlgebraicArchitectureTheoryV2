//! 整数環 $\mathbb{Z}$ 上の `solver/lift_z` 補助解析（`T_raw`・相対 cone `F_u`・宣言被覆・アフィン修復）。

use crate::algebra::artin_quotient::SquareZeroExtension;
use crate::algebra::cochain::{CochainComplex, smith_normal_form_z};
use crate::algebra::linear::{AffineSolutionZ, solve_affine_z};
use crate::algebra::poly::{AlgebraError, Poly};
use crate::algebra::poly_expr::{ExprBindings, VarOrder};
use crate::algebra::syzygy::jacobian_polys;
use crate::ir::lift::{DeclarationCoverSpec, LiftTaskSpec, RelativeReadingSpec};
use crate::ir::result::SilenceReason;
use crate::ir::result_phase4::{
    DeclarationCoverResult, RawCechComparisonResult, RelativeConeResult,
};
use crate::ir::term::PolyExpr;
use crate::solver::lift_common::{
    apply_m_shift, check_cover_support_closure, concat_vecs, eval_var_coords_generic,
    expand_subset_delta, expr_supported_in, format_var_map, grad_vanishes_on_basis,
    map_lift_algebra_error, reevaluate_laws_in_rp, write_block,
};
use crate::solver::lift_z::CoreLiftZ;
use num_bigint::BigInt;
use num_traits::Zero;
use std::collections::{BTreeMap, BTreeSet};

pub(crate) fn compute_raw_cech_z(
    complex_d: &CochainComplex<BigInt>,
    h1_d_dim: usize,
) -> Result<RawCechComparisonResult, SilenceReason> {
    let t_raw = CochainComplex::new(
        complex_d.dim0(),
        complex_d.dim1(),
        0,
        complex_d.d0().to_vec(),
        Vec::new(),
        BigInt::zero(),
    )
    .map_err(map_lift_algebra_error)?;
    let raw_coh = t_raw.cohomology_z().map_err(map_lift_algebra_error)?;
    let d1_rank = if complex_d.dim2() == 0 {
        0
    } else {
        smith_normal_form_z(complex_d.d1(), complex_d.dim1())
            .map_err(map_lift_algebra_error)?
            .rank
    };
    Ok(RawCechComparisonResult {
        h0_t_raw_dim: raw_coh.h0.free_rank,
        h1_t_raw_dim: raw_coh.h1.free_rank,
        h1_d_dim,
        kernel_map_exact_verified: raw_coh.h1.free_rank == h1_d_dim + d1_rank,
        differs_from_full_syzygy: raw_coh.h1.free_rank != h1_d_dim,
    })
}

pub(crate) struct ComputedRelativeConeZ {
    pub(crate) result: RelativeConeResult,
    pub(crate) fu: CochainComplex<BigInt>,
    pub(crate) rel_cocycle: Vec<BigInt>,
    pub(crate) raw_val_rp: Option<(Vec<BigInt>, bool)>,
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn compute_relative_cone_z(
    spec: &LiftTaskSpec,
    rel: &RelativeReadingSpec,
    law_polys: &[Poly<BigInt>],
    vars: &VarOrder,
    bindings: &ExprBindings,
    ext: &SquareZeroExtension<BigInt>,
    base_pt_r: &[Vec<BigInt>],
    param_vals_r: &[Vec<BigInt>],
    ambient_lift_rp: &[Vec<BigInt>],
    param_vals_rp: &[Vec<BigInt>],
    core: &CoreLiftZ,
) -> Result<ComputedRelativeConeZ, SilenceReason> {
    if !rel.obs_laws.is_empty() {
        return Err(SilenceReason::SyzygyOutOfScope {
            detail: "relative cone with non-empty obs_laws over Z is out of scope".to_owned(),
        });
    }
    let n = spec.variables.len();
    let r = law_polys.len();
    let m = rel.obs_vars.len();
    let dm = ext.kernel_dim();
    let z = BigInt::zero();

    let rm_map: BTreeMap<&str, &PolyExpr> = rel
        .reading_map
        .iter()
        .map(|(k, v)| (k.as_str(), v))
        .collect();
    let mut reading_polys = Vec::with_capacity(m);
    for ov in &rel.obs_vars {
        reading_polys
            .push(Poly::from_expr_z(rm_map[ov.as_str()], bindings).map_err(map_lift_algebra_error)?);
    }

    let obs_lift_rp =
        eval_var_coords_generic(&rel.obs_vars, &rel.designated_obs_lift, &Poly::from_expr_z)
            .map_err(map_lift_algebra_error)?;
    let base_full_r = concat_vecs(base_pt_r, param_vals_r);
    for (idx, (rp_poly, y_rp)) in reading_polys.iter().zip(&obs_lift_rp).enumerate() {
        let expected_r = ext
            .r_base()
            .eval_poly(rp_poly, &base_full_r)
            .map_err(map_lift_algebra_error)?;
        if expected_r != ext.project(y_rp) {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "designated_obs_lift_covers_base_reading".to_owned(),
                detail: format!("designated_obs_lift `{}` mismatch in R", rel.obs_vars[idx]),
            });
        }
    }

    let jac_rho = jacobian_polys(&reading_polys, vars.len()).map_err(map_lift_algebra_error)?;
    let mut j_rho = vec![vec![z.clone(); n * dm]; m * dm];
    for (a, jac_row) in jac_rho.iter().enumerate().take(m) {
        for (j, jac_entry) in jac_row.iter().enumerate().take(n) {
            let val_r = ext
                .r_base()
                .eval_poly(jac_entry, &base_full_r)
                .map_err(map_lift_algebra_error)?;
            let block = r_action_matrix_z(ext, &val_r).map_err(map_lift_algebra_error)?;
            write_block(&mut j_rho, a * dm, j * dm, &block);
        }
    }
    let mut d0_fu = vec![vec![z.clone(); n * dm]; (r + m) * dm];
    for (row_idx, row) in core.complex.d0().iter().enumerate() {
        d0_fu[row_idx] = row.clone();
    }
    for (row_idx, row) in j_rho.iter().enumerate() {
        d0_fu[r * dm + row_idx] = row.clone();
    }
    let q_dm = core.complex.dim2();
    let mut d1_fu = vec![vec![z.clone(); (r + m) * dm]; q_dm];
    for (row_idx, row) in core.complex.d1().iter().enumerate() {
        for (col_idx, val) in row.iter().enumerate() {
            d1_fu[row_idx][col_idx] = val.clone();
        }
    }
    let fu = CochainComplex::new(n * dm, (r + m) * dm, q_dm, d0_fu, d1_fu, z)
        .map_err(map_lift_algebra_error)?;

    let lift_full_rp = concat_vecs(ambient_lift_rp, param_vals_rp);
    let mut rel_cocycle = core.residual_m.clone();
    for (rp_poly, y_rp) in reading_polys.iter().zip(&obs_lift_rp) {
        let read_val = ext
            .r_prime()
            .eval_poly(rp_poly, &lift_full_rp)
            .map_err(map_lift_algebra_error)?;
        let diff = ext.r_prime().sub(&read_val, y_rp);
        rel_cocycle.extend(
            ext.extract_kernel_coords_z(&diff)
                .map_err(map_lift_algebra_error)?,
        );
    }

    let fu_coh = fu.cohomology_z().map_err(map_lift_algebra_error)?;
    let fu_coc = fu
        .check_h1_cocycle_z(&rel_cocycle)
        .map_err(map_lift_algebra_error)?;
    if !fu_coc.is_cocycle {
        return Err(SilenceReason::SyzygyOutOfScope {
            detail: "Z relative cone cocycle verification failed".to_owned(),
        });
    }
    let relative_obstruction_is_zero = fu_coc.is_zero_in_z;

    let (restored_relative_lift, reevaluation, restored_shifted) =
        if let Some(witness_pos) = fu_coc.coboundary_witness_z {
            let delta: Vec<BigInt> = witness_pos.iter().map(|v| -v).collect();
            let shifted =
                apply_m_shift(ext, ambient_lift_rp, &delta).map_err(map_lift_algebra_error)?;
            let mut reeval = reevaluate_laws_in_rp(law_polys, &shifted, param_vals_rp, ext)
                .map_err(map_lift_algebra_error)?;
            let shifted_full = concat_vecs(&shifted, param_vals_rp);
            let mut obs_bad = Vec::new();
            for (idx, (rp_poly, y_rp)) in reading_polys.iter().zip(&obs_lift_rp).enumerate() {
                let got = ext
                    .r_prime()
                    .eval_poly(rp_poly, &shifted_full)
                    .map_err(map_lift_algebra_error)?;
                if got != *y_rp {
                    obs_bad.push(format!(
                        "{}={} (expected {})",
                        rel.obs_vars[idx],
                        ext.r_prime().format_elem(&got),
                        ext.r_prime().format_elem(y_rp)
                    ));
                }
            }
            if !obs_bad.is_empty() {
                reeval.matched = false;
                reeval.detail = format!("{}; obs mismatch: {}", reeval.detail, obs_bad.join(", "));
            } else {
                reeval.detail = format!("{}; designated obs lift matched", reeval.detail);
            }
            let fmt = format_var_map(&spec.variables, &shifted, ext.r_prime());
            (Some(fmt), Some(reeval), Some(shifted))
        } else {
            (None, None, None)
        };

    let (raw_read_diff_value, raw_read_diff_signed_match, raw_val_rp) =
        if let Some(rr) = &rel.raw_read_diff {
            let rr_poly = Poly::from_expr_z(&rr.expr, bindings).map_err(map_lift_algebra_error)?;
            let z_c = BigInt::zero();
            let mut grad_rr = vec![vec![z_c.clone(); n * dm]; dm];
            for j in 0..n {
                let dp = rr_poly.partial_derivative(j).map_err(map_lift_algebra_error)?;
                let val_r = ext
                    .r_base()
                    .eval_poly(&dp, &base_full_r)
                    .map_err(map_lift_algebra_error)?;
                let blk = r_action_matrix_z(ext, &val_r).map_err(map_lift_algebra_error)?;
                write_block(&mut grad_rr, 0, j * dm, &blk);
            }
            if relative_obstruction_is_zero {
                if let Some(shifted) = &restored_shifted {
                    if grad_vanishes_on_basis(&grad_rr, &fu_coh.h0_basis, &z_c) {
                        let eval_full = concat_vecs(shifted, param_vals_rp);
                        let raw_val = ext
                            .r_prime()
                            .eval_poly(&rr_poly, &eval_full)
                            .map_err(map_lift_algebra_error)?;
                        let matched = Some(ext.r_prime().is_zero_elem(&raw_val));
                        let formatted = ext.r_prime().format_elem(&raw_val);
                        (Some(formatted), matched, Some((raw_val, rr.negated)))
                    } else {
                        (None, None, None)
                    }
                } else {
                    (None, None, None)
                }
            } else if let Some((eval_base, ker_j_rho)) = align_ambient_to_obs_z(
                ambient_lift_rp,
                &j_rho,
                &reading_polys,
                &obs_lift_rp,
                param_vals_rp,
                ext,
            ) {
                if grad_vanishes_on_basis(&grad_rr, &ker_j_rho, &z_c) {
                    let eval_full = concat_vecs(&eval_base, param_vals_rp);
                    let raw_val = ext
                        .r_prime()
                        .eval_poly(&rr_poly, &eval_full)
                        .map_err(map_lift_algebra_error)?;
                    let formatted = ext.r_prime().format_elem(&raw_val);
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

    Ok(ComputedRelativeConeZ {
        result: RelativeConeResult {
            h0_fu_dim: fu_coh.h0.free_rank,
            h1_fu_dim: fu_coh.h1.free_rank,
            relative_obstruction_coords: if relative_obstruction_is_zero {
                Vec::new()
            } else {
                rel_cocycle.iter().map(ToString::to_string).collect()
            },
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

#[allow(clippy::too_many_arguments)]
pub(crate) fn compute_declaration_cover_z(
    spec: &LiftTaskSpec,
    cov: &DeclarationCoverSpec,
    law_polys: &[Poly<BigInt>],
    ext: &SquareZeroExtension<BigInt>,
    base_pt_r: &[Vec<BigInt>],
    param_vals_r: &[Vec<BigInt>],
    ambient_lift_rp: &[Vec<BigInt>],
    param_vals_rp: &[Vec<BigInt>],
    core: &CoreLiftZ,
    rel_cone: Option<&mut ComputedRelativeConeZ>,
) -> Result<DeclarationCoverResult, SilenceReason> {
    let (support_closed, unclosed_observations) = check_cover_support_closure(
        cov,
        &spec.variables,
        &spec.laws,
        spec.relative_reading.as_ref(),
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

    let (p_l, k_l) = solve_context_local_lift_z(
        spec,
        &left_ctx.vars,
        &left_ctx.laws,
        law_polys,
        ext,
        base_pt_r,
        param_vals_r,
        ambient_lift_rp,
        param_vals_rp,
    )?;
    let (p_r, k_r) = solve_context_local_lift_z(
        spec,
        &right_ctx.vars,
        &right_ctx.laws,
        law_polys,
        ext,
        base_pt_r,
        param_vals_r,
        ambient_lift_rp,
        param_vals_rp,
    )?;

    let var_idx: BTreeMap<&str, usize> = spec
        .variables
        .iter()
        .enumerate()
        .map(|(i, v)| (v.as_str(), i))
        .collect();
    let left_vars: BTreeSet<&str> = left_ctx.vars.iter().map(String::as_str).collect();
    let right_vars: BTreeSet<&str> = right_ctx.vars.iter().map(String::as_str).collect();
    let overlap_indices: Vec<usize> = spec
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
    let dm = ext.kernel_dim();
    let mut rhs_o = Vec::with_capacity(overlap_indices.len() * dm);
    for &idx in &overlap_indices {
        for k in 0..dm {
            rhs_o.push(&p_r[idx * dm + k] - &p_l[idx * dm + k]);
        }
    }
    let total_k = k_l.len() + k_r.len();
    let mut cob_mat = vec![vec![BigInt::zero(); total_k]; rhs_o.len()];
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
                cob_mat[o_pos * dm + k][c_idx] = -&kb[v_idx * dm + k];
            }
        }
    }
    let (cech_class_nonzero, left_delta, right_delta) = if total_k == 0 {
        let nonzero = rhs_o.iter().any(|v| !v.is_zero());
        (nonzero, p_l, p_r)
    } else {
        match solve_affine_z(&cob_mat, &rhs_o, total_k).map_err(map_lift_algebra_error)? {
            AffineSolutionZ::Consistent { particular, .. } => {
                let mut adj_l = p_l;
                for (c, kb) in particular[..k_l.len()].iter().zip(&k_l) {
                    if !c.is_zero() {
                        for (dst, src) in adj_l.iter_mut().zip(kb) {
                            *dst += c * src;
                        }
                    }
                }
                let mut adj_r = p_r;
                for (c, kb) in particular[k_l.len()..].iter().zip(&k_r) {
                    if !c.is_zero() {
                        for (dst, src) in adj_r.iter_mut().zip(kb) {
                            *dst += c * src;
                        }
                    }
                }
                (false, adj_l, adj_r)
            }
            AffineSolutionZ::Inconsistent { .. } => (true, p_l, p_r),
        }
    };

    let left_lift =
        apply_m_shift(ext, ambient_lift_rp, &left_delta).map_err(map_lift_algebra_error)?;
    let right_lift =
        apply_m_shift(ext, ambient_lift_rp, &right_delta).map_err(map_lift_algebra_error)?;

    let mut diff_map = BTreeMap::new();
    for (sv, &idx) in cech.shared_vars.iter().zip(&shared_indices) {
        let d = ext.r_prime().sub(&right_lift[idx], &left_lift[idx]);
        diff_map.insert(sv.clone(), ext.r_prime().format_elem(&d));
    }

    let matches_relative_obstruction = if let Some(rc) = rel_cone {
        let left_laws: BTreeSet<&str> = left_ctx.laws.iter().map(String::as_str).collect();
        let mut overlap_diff = vec![BigInt::zero(); spec.variables.len() * dm];
        for &j in &overlap_indices {
            for k in 0..dm {
                overlap_diff[j * dm + k] = &right_delta[j * dm + k] - &left_delta[j * dm + k];
            }
        }
        let mut mv_cocycle = vec![BigInt::zero(); rc.fu.dim1()];
        for (i, law) in spec.laws.iter().enumerate() {
            if left_laws.contains(law.name.as_str()) {
                for row_k in 0..dm {
                    let row = &core.complex.d0()[i * dm + row_k];
                    let mut acc = BigInt::zero();
                    for (a, b) in row.iter().zip(&overlap_diff) {
                        if !a.is_zero() && !b.is_zero() {
                            acc += a * b;
                        }
                    }
                    mv_cocycle[i * dm + row_k] = acc;
                }
            }
        }
        if let Some(rel) = &spec.relative_reading {
            let rm_map: BTreeMap<&str, &PolyExpr> = rel
                .reading_map
                .iter()
                .map(|(k, v)| (k.as_str(), v))
                .collect();
            let r_offset = spec.laws.len() * dm;
            for (a, ov) in rel.obs_vars.iter().enumerate() {
                if expr_supported_in(rm_map[ov.as_str()], &left_vars) {
                    for row_k in 0..dm {
                        let row = &rc.fu.d0()[r_offset + a * dm + row_k];
                        let mut acc = BigInt::zero();
                        for (c_val, b) in row.iter().zip(&overlap_diff) {
                            if !c_val.is_zero() && !b.is_zero() {
                                acc += c_val * b;
                            }
                        }
                        mv_cocycle[r_offset + a * dm + row_k] = acc;
                    }
                }
            }
        }
        let mv_is_cocycle = rc.fu.d1().iter().all(|row| {
            let mut acc = BigInt::zero();
            for (a, b) in row.iter().zip(&mv_cocycle) {
                if !a.is_zero() && !b.is_zero() {
                    acc += a * b;
                }
            }
            acc.is_zero()
        });
        let class_diff: Vec<BigInt> = rc
            .rel_cocycle
            .iter()
            .zip(&mv_cocycle)
            .map(|(a, b)| a - b)
            .collect();
        let class_matches = mv_is_cocycle
            && matches!(
                solve_affine_z(rc.fu.d0(), &class_diff, rc.fu.dim0()),
                Ok(AffineSolutionZ::Consistent { .. })
            );

        if let Some((raw_val, negated)) = &rc.raw_val_rp
            && !rc.result.relative_obstruction_is_zero
            && shared_indices.len() == 1
        {
            let target_rp = if *negated {
                ext.r_prime().neg(raw_val)
            } else {
                raw_val.clone()
            };
            let oriented_match = match ext.extract_kernel_coords_z(&target_rp) {
                Ok(target_m) => {
                    let target_var_idx = shared_indices[0];
                    let mut target_overlap = vec![BigInt::zero(); rhs_o.len()];
                    if let Some(o_pos) = overlap_indices.iter().position(|&v| v == target_var_idx) {
                        for k in 0..dm {
                            target_overlap[o_pos * dm + k] = target_m[k].clone();
                        }
                    }
                    let residual: Vec<BigInt> = rhs_o
                        .iter()
                        .zip(&target_overlap)
                        .map(|(a, b)| a - b)
                        .collect();
                    if total_k == 0 {
                        residual.iter().all(Zero::is_zero)
                    } else {
                        matches!(
                            solve_affine_z(&cob_mat, &residual, total_k),
                            Ok(AffineSolutionZ::Consistent { .. })
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

#[allow(clippy::too_many_arguments, clippy::type_complexity)]
fn solve_context_local_lift_z(
    spec: &LiftTaskSpec,
    ctx_var_names: &[String],
    ctx_law_names: &[String],
    law_polys: &[Poly<BigInt>],
    ext: &SquareZeroExtension<BigInt>,
    base_pt_r: &[Vec<BigInt>],
    param_vals_r: &[Vec<BigInt>],
    ambient_lift_rp: &[Vec<BigInt>],
    param_vals_rp: &[Vec<BigInt>],
) -> Result<(Vec<BigInt>, Vec<Vec<BigInt>>), SilenceReason> {
    let n = spec.variables.len();
    let dm = ext.kernel_dim();
    let z = BigInt::zero();
    let ctx_var_set: BTreeSet<&str> = ctx_var_names.iter().map(String::as_str).collect();
    let ctx_var_indices: Vec<usize> = spec
        .variables
        .iter()
        .enumerate()
        .filter(|(_, v)| ctx_var_set.contains(v.as_str()))
        .map(|(i, _)| i)
        .collect();
    let num_cols = ctx_var_indices.len() * dm;
    let law_set: BTreeSet<&str> = ctx_law_names.iter().map(String::as_str).collect();
    let active_laws: Vec<&Poly<BigInt>> = spec
        .laws
        .iter()
        .zip(law_polys)
        .filter(|(l, _)| law_set.contains(l.name.as_str()))
        .map(|(_, p)| p)
        .collect();

    let param_names: Vec<String> = spec.ring_params.iter().map(|p| p.name.clone()).collect();
    let (_, bindings) = ExprBindings::from_slices(&spec.variables, &[], &param_names)
        .map_err(map_lift_algebra_error)?;
    let base_full_r = concat_vecs(base_pt_r, param_vals_r);
    let lift_full_rp = concat_vecs(ambient_lift_rp, param_vals_rp);

    let mut rows = Vec::new();
    let mut rhs = Vec::new();
    for poly in &active_laws {
        let val_rp = ext
            .r_prime()
            .eval_poly(poly, &lift_full_rp)
            .map_err(map_lift_algebra_error)?;
        let res_m = ext
            .extract_kernel_coords_z(&val_rp)
            .map_err(map_lift_algebra_error)?;
        let mut row_block = vec![vec![z.clone(); num_cols]; dm];
        for (c_pos, &j) in ctx_var_indices.iter().enumerate() {
            let dp = poly.partial_derivative(j).map_err(map_lift_algebra_error)?;
            let val_r = ext
                .r_base()
                .eval_poly(&dp, &base_full_r)
                .map_err(map_lift_algebra_error)?;
            let blk = r_action_matrix_z(ext, &val_r).map_err(map_lift_algebra_error)?;
            write_block(&mut row_block, 0, c_pos * dm, &blk);
        }
        rows.extend(row_block);
        rhs.extend(res_m.into_iter().map(|v| -v));
    }
    if let Some(rel) = &spec.relative_reading {
        let obs_lift_rp =
            eval_var_coords_generic(&rel.obs_vars, &rel.designated_obs_lift, &Poly::from_expr_z)
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
            let rp_poly = Poly::from_expr_z(expr, &bindings).map_err(map_lift_algebra_error)?;
            let read_val = ext
                .r_prime()
                .eval_poly(&rp_poly, &lift_full_rp)
                .map_err(map_lift_algebra_error)?;
            let diff = ext.r_prime().sub(&read_val, y_rp);
            let w_m = ext
                .extract_kernel_coords_z(&diff)
                .map_err(map_lift_algebra_error)?;
            let mut row_block = vec![vec![z.clone(); num_cols]; dm];
            for (c_pos, &j) in ctx_var_indices.iter().enumerate() {
                let dp = rp_poly.partial_derivative(j).map_err(map_lift_algebra_error)?;
                let val_r = ext
                    .r_base()
                    .eval_poly(&dp, &base_full_r)
                    .map_err(map_lift_algebra_error)?;
                let blk = r_action_matrix_z(ext, &val_r).map_err(map_lift_algebra_error)?;
                write_block(&mut row_block, 0, c_pos * dm, &blk);
            }
            rows.extend(row_block);
            rhs.extend(w_m.into_iter().map(|v| -v));
        }
    }

    match solve_affine_z(&rows, &rhs, num_cols).map_err(map_lift_algebra_error)? {
        AffineSolutionZ::Consistent {
            particular,
            kernel_basis,
            ..
        } => {
            let full_p = expand_subset_delta(n, &ctx_var_indices, dm, &particular, &z);
            let full_k = kernel_basis
                .iter()
                .map(|kb| expand_subset_delta(n, &ctx_var_indices, dm, kb, &z))
                .collect();
            Ok((full_p, full_k))
        }
        AffineSolutionZ::Inconsistent { .. } => Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "two_context_local_lift_exists".to_owned(),
            detail: "Z local lift does not exist on one of the two contexts".to_owned(),
        }),
    }
}

pub(crate) fn r_action_matrix_z(
    ext: &SquareZeroExtension<BigInt>,
    a_in_r: &[BigInt],
) -> Result<Vec<Vec<BigInt>>, AlgebraError> {
    let dm = ext.kernel_dim();
    let a_lift = match solve_affine_z(ext.projection(), a_in_r, ext.r_prime().dim())? {
        AffineSolutionZ::Consistent { particular, .. } => particular,
        AffineSolutionZ::Inconsistent { .. } => {
            return Err(AlgebraError::OutOfScope {
                detail: "Z projection R' -> R is not surjective".to_owned(),
            });
        }
    };
    let mut block = vec![vec![BigInt::zero(); dm]; dm];
    for (col, kb) in ext.kernel_basis().iter().enumerate() {
        let prod = ext.r_prime().mul(&a_lift, kb);
        let coords = ext.extract_kernel_coords_z(&prod)?;
        for (row, val) in coords.into_iter().enumerate() {
            block[row][col] = val;
        }
    }
    Ok(block)
}

#[allow(clippy::type_complexity)]
fn align_ambient_to_obs_z(
    ambient_lift_rp: &[Vec<BigInt>],
    j_rho: &[Vec<BigInt>],
    reading_polys: &[Poly<BigInt>],
    obs_lift_rp: &[Vec<BigInt>],
    param_vals_rp: &[Vec<BigInt>],
    ext: &SquareZeroExtension<BigInt>,
) -> Option<(Vec<Vec<BigInt>>, Vec<Vec<BigInt>>)> {
    let full = concat_vecs(ambient_lift_rp, param_vals_rp);
    let mut neg_w = Vec::new();
    for (rp_poly, y_rp) in reading_polys.iter().zip(obs_lift_rp) {
        let got = ext.r_prime().eval_poly(rp_poly, &full).ok()?;
        let diff = ext.r_prime().sub(y_rp, &got);
        neg_w.extend(ext.extract_kernel_coords_z(&diff).ok()?);
    }
    let num_cols = ambient_lift_rp.len() * ext.kernel_dim();
    match solve_affine_z(j_rho, &neg_w, num_cols).ok()? {
        AffineSolutionZ::Consistent {
            particular,
            kernel_basis,
            ..
        } => Some((apply_m_shift(ext, ambient_lift_rp, &particular).ok()?, kernel_basis)),
        AffineSolutionZ::Inconsistent { .. } => None,
    }
}

