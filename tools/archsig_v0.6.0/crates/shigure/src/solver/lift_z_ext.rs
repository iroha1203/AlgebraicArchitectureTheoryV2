//! 整数環 $\mathbb{Z}$ 上の `solver/lift_z` 補助解析（`T_raw`・相対 cone `F_u`・宣言被覆・アフィン修復）。

use crate::algebra::artin_quotient::SquareZeroExtension;
use crate::algebra::cochain::{CochainComplex, smith_normal_form_z};
use crate::algebra::linear::{AffineSolutionZ, solve_affine_z};
use crate::algebra::poly::{AlgebraError, Poly};
use crate::algebra::poly_expr::{ExprBindings, VarOrder};
use crate::algebra::syzygy::jacobian_polys;
use crate::ir::lift::{
    AffineAllowedSpec, DeclarationCoverSpec, LiftTaskSpec, RelativeReadingSpec,
};
use crate::ir::result::SilenceReason;
use crate::ir::result_phase4::{
    AffineRepairResult, DeclarationCoverResult, RawCechComparisonResult, RelativeConeResult,
};
use crate::ir::term::PolyExpr;
use crate::solver::lift_common::{
    apply_m_shift, apply_rp_subset_shift, check_cover_support_closure, concat_vecs,
    eval_var_coords_generic, expand_subset_delta, format_subset_m_map, format_subset_rp_map,
    format_var_map, map_lift_algebra_error, reevaluate_laws_in_rp, write_block,
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
) -> Result<RelativeConeResult, SilenceReason> {
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

    let (restored_relative_lift, reevaluation) =
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
            (
                Some(format_var_map(&spec.variables, &shifted, ext.r_prime())),
                Some(reeval),
            )
        } else {
            (None, None)
        };

    let (raw_read_diff_value, raw_read_diff_signed_match) = if let Some(rr) = &rel.raw_read_diff {
        let rr_poly = Poly::from_expr_z(&rr.expr, bindings).map_err(map_lift_algebra_error)?;
        let eval_base = align_ambient_to_obs_z(
            ambient_lift_rp,
            &j_rho,
            &reading_polys,
            &obs_lift_rp,
            param_vals_rp,
            ext,
        )
        .unwrap_or_else(|| ambient_lift_rp.to_vec());
        let eval_full = concat_vecs(&eval_base, param_vals_rp);
        let raw_val = ext
            .r_prime()
            .eval_poly(&rr_poly, &eval_full)
            .map_err(map_lift_algebra_error)?;
        let matched = if relative_obstruction_is_zero {
            ext.r_prime().is_zero_elem(&raw_val)
        } else {
            compare_raw_diff_in_fu_z(&raw_val, rr.negated, r, &fu, &rel_cocycle, ext)
        };
        (Some(ext.r_prime().format_elem(&raw_val)), Some(matched))
    } else {
        (None, None)
    };

    Ok(RelativeConeResult {
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
    rel_cone: Option<&RelativeConeResult>,
) -> Result<DeclarationCoverResult, SilenceReason> {
    let (support_closed, unclosed_observations) = check_cover_support_closure(cov, &spec.laws);
    let Some(cech) = &cov.two_context_cech else {
        return Ok(DeclarationCoverResult {
            support_closed,
            unclosed_observations,
            two_context_cech_diff: None,
            matches_relative_obstruction: None,
        });
    };
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
    let shared_indices: Vec<usize> = cech
        .shared_vars
        .iter()
        .map(|sv| var_idx[sv.as_str()])
        .collect();
    let dm = ext.kernel_dim();
    let mut rhs_s = Vec::with_capacity(shared_indices.len() * dm);
    for &idx in &shared_indices {
        for k in 0..dm {
            rhs_s.push(&p_r[idx * dm + k] - &p_l[idx * dm + k]);
        }
    }
    let total_k = k_l.len() + k_r.len();
    let (cech_class_nonzero, left_delta, right_delta) = if total_k == 0 {
        let nonzero = rhs_s.iter().any(|v| !v.is_zero());
        (nonzero, p_l, p_r)
    } else {
        let mut cob_mat = vec![vec![BigInt::zero(); total_k]; rhs_s.len()];
        for (c_idx, kb) in k_l.iter().enumerate() {
            for (s_pos, &v_idx) in shared_indices.iter().enumerate() {
                for k in 0..dm {
                    cob_mat[s_pos * dm + k][c_idx] = kb[v_idx * dm + k].clone();
                }
            }
        }
        for (c_off, kb) in k_r.iter().enumerate() {
            let c_idx = k_l.len() + c_off;
            for (s_pos, &v_idx) in shared_indices.iter().enumerate() {
                for k in 0..dm {
                    cob_mat[s_pos * dm + k][c_idx] = -&kb[v_idx * dm + k];
                }
            }
        }
        match solve_affine_z(&cob_mat, &rhs_s, total_k).map_err(map_lift_algebra_error)? {
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
    let matches_relative_obstruction = rel_cone
        .map(|rc| rc.relative_obstruction_is_zero != cech_class_nonzero);
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
        let mut row_block = vec![vec![z.clone(); n * dm]; dm];
        for j in 0..n {
            let dp = poly.partial_derivative(j).map_err(map_lift_algebra_error)?;
            let val_r = ext
                .r_base()
                .eval_poly(&dp, &base_full_r)
                .map_err(map_lift_algebra_error)?;
            let blk = r_action_matrix_z(ext, &val_r).map_err(map_lift_algebra_error)?;
            write_block(&mut row_block, 0, j * dm, &blk);
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
            let rp_poly =
                Poly::from_expr_z(rm_map[ov.as_str()], &bindings).map_err(map_lift_algebra_error)?;
            let read_val = ext
                .r_prime()
                .eval_poly(&rp_poly, &lift_full_rp)
                .map_err(map_lift_algebra_error)?;
            let diff = ext.r_prime().sub(&read_val, y_rp);
            let w_m = ext
                .extract_kernel_coords_z(&diff)
                .map_err(map_lift_algebra_error)?;
            let mut row_block = vec![vec![z.clone(); n * dm]; dm];
            for j in 0..n {
                let dp = rp_poly.partial_derivative(j).map_err(map_lift_algebra_error)?;
                let val_r = ext
                    .r_base()
                    .eval_poly(&dp, &base_full_r)
                    .map_err(map_lift_algebra_error)?;
                let blk = r_action_matrix_z(ext, &val_r).map_err(map_lift_algebra_error)?;
                write_block(&mut row_block, 0, j * dm, &blk);
            }
            rows.extend(row_block);
            rhs.extend(w_m.into_iter().map(|v| -v));
        }
    }

    match solve_affine_z(&rows, &rhs, n * dm).map_err(map_lift_algebra_error)? {
        AffineSolutionZ::Consistent {
            particular,
            kernel_basis,
            ..
        } => Ok((particular, kernel_basis)),
        AffineSolutionZ::Inconsistent { .. } => Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "two_context_local_lift_exists".to_owned(),
            detail: "Z local lift does not exist on one of the two contexts".to_owned(),
        }),
    }
}

pub(crate) fn compute_affine_repair_z(
    spec: &LiftTaskSpec,
    aff: &AffineAllowedSpec,
    law_polys: &[Poly<BigInt>],
    ext: &SquareZeroExtension<BigInt>,
    ambient_lift_rp: &[Vec<BigInt>],
    param_vals_rp: &[Vec<BigInt>],
    core: &CoreLiftZ,
) -> Result<AffineRepairResult, SilenceReason> {
    let var_idx: BTreeMap<&str, usize> = spec
        .variables
        .iter()
        .enumerate()
        .map(|(i, v)| (v.as_str(), i))
        .collect();
    let allowed_indices: Vec<usize> = aff.allowed_vars.iter().map(|v| var_idx[v.as_str()]).collect();
    let dm = ext.kernel_dim();
    let z = BigInt::zero();

    if aff.finite_displacement {
        let dp = ext.r_prime().dim();
        let full_base = concat_vecs(ambient_lift_rp, param_vals_rp);
        for poly in law_polys {
            for mono in poly.terms().keys() {
                let deg_allowed: u32 = allowed_indices.iter().map(|&idx| mono.exps()[idx]).sum();
                if deg_allowed > 1 {
                    return Err(SilenceReason::SyzygyOutOfScope {
                        detail:
                            "finite_displacement Z affine repair requires laws affine in allowed_vars"
                                .to_owned(),
                    });
                }
            }
        }
        let num_cols = allowed_indices.len() * dp;
        let mut mat = vec![vec![z; num_cols]; law_polys.len() * dp];
        let mut rhs = Vec::with_capacity(law_polys.len() * dp);
        for (i, poly) in law_polys.iter().enumerate() {
            let res_rp = ext
                .r_prime()
                .eval_poly(poly, &full_base)
                .map_err(map_lift_algebra_error)?;
            rhs.extend(ext.r_prime().neg(&res_rp));
            for (c_block, &v_idx) in allowed_indices.iter().enumerate() {
                let deriv = poly.partial_derivative(v_idx).map_err(map_lift_algebra_error)?;
                let coeff_rp = ext
                    .r_prime()
                    .eval_poly(&deriv, &full_base)
                    .map_err(map_lift_algebra_error)?;
                for col_k in 0..dp {
                    let ek = ext.r_prime().basis_elem(col_k);
                    let prod = ext.r_prime().mul(&coeff_rp, &ek);
                    for (row_k, val) in prod.into_iter().enumerate() {
                        mat[i * dp + row_k][c_block * dp + col_k] = val;
                    }
                }
            }
        }
        return match solve_affine_z(&mat, &rhs, num_cols).map_err(map_lift_algebra_error)? {
            AffineSolutionZ::Consistent {
                particular,
                kernel_basis,
                ..
            } => {
                let shifted =
                    apply_rp_subset_shift(ambient_lift_rp, &allowed_indices, dp, &particular, ext);
                let mut reeval = reevaluate_laws_in_rp(law_polys, &shifted, param_vals_rp, ext)
                    .map_err(map_lift_algebra_error)?;
                let mut torsor_maps = Vec::with_capacity(kernel_basis.len());
                for kb in &kernel_basis {
                    let shifted_k = apply_rp_subset_shift(&shifted, &allowed_indices, dp, kb, ext);
                    let re_k = reevaluate_laws_in_rp(law_polys, &shifted_k, param_vals_rp, ext)
                        .map_err(map_lift_algebra_error)?;
                    if !re_k.matched {
                        reeval.matched = false;
                    }
                    torsor_maps.push(format_subset_rp_map(&aff.allowed_vars, kb, dp, ext));
                }
                Ok(AffineRepairResult {
                    finite_displacement: true,
                    allowed_vars: aff.allowed_vars.clone(),
                    repair_exists: true,
                    particular_delta: Some(format_subset_rp_map(
                        &aff.allowed_vars,
                        &particular,
                        dp,
                        ext,
                    )),
                    torsor_basis: torsor_maps,
                    reevaluation: Some(reeval),
                })
            }
            AffineSolutionZ::Inconsistent { .. } => Ok(AffineRepairResult {
                finite_displacement: true,
                allowed_vars: aff.allowed_vars.clone(),
                repair_exists: false,
                particular_delta: None,
                torsor_basis: Vec::new(),
                reevaluation: None,
            }),
        };
    }

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
    let neg_res: Vec<BigInt> = core.residual_m.iter().map(|v| -v).collect();
    match solve_affine_z(&sub_d0, &neg_res, num_cols).map_err(map_lift_algebra_error)? {
        AffineSolutionZ::Consistent {
            particular,
            kernel_basis,
            ..
        } => {
            let full_delta = expand_subset_delta(
                spec.variables.len(),
                &allowed_indices,
                dm,
                &particular,
                &z,
            );
            let shifted =
                apply_m_shift(ext, ambient_lift_rp, &full_delta).map_err(map_lift_algebra_error)?;
            let mut reeval = reevaluate_laws_in_rp(law_polys, &shifted, param_vals_rp, ext)
                .map_err(map_lift_algebra_error)?;
            let mut torsor_maps = Vec::with_capacity(kernel_basis.len());
            for kb in &kernel_basis {
                let kb_full =
                    expand_subset_delta(spec.variables.len(), &allowed_indices, dm, kb, &z);
                let shifted_k =
                    apply_m_shift(ext, &shifted, &kb_full).map_err(map_lift_algebra_error)?;
                let re_k = reevaluate_laws_in_rp(law_polys, &shifted_k, param_vals_rp, ext)
                    .map_err(map_lift_algebra_error)?;
                if !re_k.matched {
                    reeval.matched = false;
                }
                torsor_maps.push(format_subset_m_map(&aff.allowed_vars, kb, ext));
            }
            Ok(AffineRepairResult {
                finite_displacement: false,
                allowed_vars: aff.allowed_vars.clone(),
                repair_exists: true,
                particular_delta: Some(format_subset_m_map(&aff.allowed_vars, &particular, ext)),
                torsor_basis: torsor_maps,
                reevaluation: Some(reeval),
            })
        }
        AffineSolutionZ::Inconsistent { .. } => Ok(AffineRepairResult {
            finite_displacement: false,
            allowed_vars: aff.allowed_vars.clone(),
            repair_exists: false,
            particular_delta: None,
            torsor_basis: Vec::new(),
            reevaluation: None,
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

fn align_ambient_to_obs_z(
    ambient_lift_rp: &[Vec<BigInt>],
    j_rho: &[Vec<BigInt>],
    reading_polys: &[Poly<BigInt>],
    obs_lift_rp: &[Vec<BigInt>],
    param_vals_rp: &[Vec<BigInt>],
    ext: &SquareZeroExtension<BigInt>,
) -> Option<Vec<Vec<BigInt>>> {
    let full = concat_vecs(ambient_lift_rp, param_vals_rp);
    let mut neg_w = Vec::new();
    for (rp_poly, y_rp) in reading_polys.iter().zip(obs_lift_rp) {
        let got = ext.r_prime().eval_poly(rp_poly, &full).ok()?;
        let diff = ext.r_prime().sub(y_rp, &got);
        neg_w.extend(ext.extract_kernel_coords_z(&diff).ok()?);
    }
    let num_cols = ambient_lift_rp.len() * ext.kernel_dim();
    match solve_affine_z(j_rho, &neg_w, num_cols).ok()? {
        AffineSolutionZ::Consistent { particular, .. } => {
            apply_m_shift(ext, ambient_lift_rp, &particular).ok()
        }
        AffineSolutionZ::Inconsistent { .. } => None,
    }
}

fn compare_raw_diff_in_fu_z(
    raw_val: &[BigInt],
    negated: bool,
    num_laws: usize,
    fu: &CochainComplex<BigInt>,
    rel_cocycle: &[BigInt],
    ext: &SquareZeroExtension<BigInt>,
) -> bool {
    let target_rp = if negated {
        ext.r_prime().neg(raw_val)
    } else {
        raw_val.to_vec()
    };
    let Ok(target_m) = ext.extract_kernel_coords_z(&target_rp) else {
        return false;
    };
    let dm = ext.kernel_dim();
    let Some(i0) = (0..num_laws).find(|&i| {
        let mut iota = vec![BigInt::zero(); fu.dim1()];
        for k in 0..dm {
            iota[i * dm + k] = target_m[k].clone();
        }
        matches!(
            solve_affine_z(fu.d0(), &iota, fu.dim0()),
            Ok(AffineSolutionZ::Inconsistent { .. })
        )
    }) else {
        return false;
    };
    let mut diff = rel_cocycle.to_vec();
    for k in 0..dm {
        diff[i0 * dm + k] = &diff[i0 * dm + k] - &target_m[k];
    }
    matches!(
        solve_affine_z(fu.d0(), &diff, fu.dim0()),
        Ok(AffineSolutionZ::Consistent { .. })
    )
}

