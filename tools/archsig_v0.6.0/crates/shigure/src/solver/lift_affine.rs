//! 許容部分加群 `H` 上のアフィン修復全解（微小・有限変位、体係数および $\mathbb{Z}$ 係数共通）（G-141 E6・H1）。

use crate::algebra::artin::{AffineSolutionField, solve_affine_field};
use crate::algebra::artin_quotient::SquareZeroExtension;
use crate::algebra::cochain::CochainComplex;
use crate::algebra::linear::{AffineSolutionZ, solve_affine_z};
use crate::algebra::poly::{AlgebraError, Poly};
use crate::algebra::scalar::RingCoeff;
use crate::algebra::syzygy::FieldCoeff;
use crate::ir::lift::{AffineAllowedSpec, LiftTaskSpec};
use crate::ir::result::SilenceReason;
use crate::ir::result_phase4::AffineRepairResult;
use crate::solver::lift::CoreLiftField;
use crate::solver::lift_common::{
    apply_m_shift, apply_rp_subset_shift, concat_vecs, expand_subset_delta, format_subset_m_map,
    format_subset_rp_map, map_lift_algebra_error, reevaluate_laws_in_rp,
};
use crate::solver::lift_z::CoreLiftZ;
use num_bigint::BigInt;
use std::collections::BTreeMap;

type LinearSolveResult<C> = Result<Option<(Vec<C>, Vec<Vec<C>>)>, AlgebraError>;

/// 体係数上の許容部分加群 `H` アフィン修復全解（G-141 E6・H1）。
pub(crate) fn compute_affine_repair_field<C: FieldCoeff>(
    spec: &LiftTaskSpec,
    aff: &AffineAllowedSpec,
    law_polys: &[Poly<C>],
    ext: &SquareZeroExtension<C>,
    ambient_lift_rp: &[Vec<C>],
    param_vals_rp: &[Vec<C>],
    core: &CoreLiftField<C>,
) -> Result<AffineRepairResult, SilenceReason> {
    let z = ext.r_prime().zero_coeff.zero_like();
    compute_affine_repair_generic(
        spec,
        aff,
        law_polys,
        ext,
        ambient_lift_rp,
        param_vals_rp,
        &core.complex,
        &core.residual_m,
        &|mat, rhs, cols| match solve_affine_field(mat, rhs, cols, &z)? {
            AffineSolutionField::Consistent {
                particular,
                kernel_basis,
                ..
            } => Ok(Some((particular, kernel_basis))),
            AffineSolutionField::Inconsistent { .. } => Ok(None),
        },
    )
}

/// 整数環 $\mathbb{Z}$ 上の許容部分加群 `H` アフィン修復全解（G-141 E6・H1）。
pub(crate) fn compute_affine_repair_z(
    spec: &LiftTaskSpec,
    aff: &AffineAllowedSpec,
    law_polys: &[Poly<BigInt>],
    ext: &SquareZeroExtension<BigInt>,
    ambient_lift_rp: &[Vec<BigInt>],
    param_vals_rp: &[Vec<BigInt>],
    core: &CoreLiftZ,
) -> Result<AffineRepairResult, SilenceReason> {
    compute_affine_repair_generic(
        spec,
        aff,
        law_polys,
        ext,
        ambient_lift_rp,
        param_vals_rp,
        &core.complex,
        &core.residual_m,
        &|mat, rhs, cols| match solve_affine_z(mat, rhs, cols)? {
            AffineSolutionZ::Consistent {
                particular,
                kernel_basis,
                ..
            } => Ok(Some((particular, kernel_basis))),
            AffineSolutionZ::Inconsistent { .. } => Ok(None),
        },
    )
}

#[allow(clippy::too_many_arguments)]
fn compute_affine_repair_generic<C, S>(
    spec: &LiftTaskSpec,
    aff: &AffineAllowedSpec,
    law_polys: &[Poly<C>],
    ext: &SquareZeroExtension<C>,
    ambient_lift_rp: &[Vec<C>],
    param_vals_rp: &[Vec<C>],
    complex: &CochainComplex<C>,
    residual_m: &[C],
    solve: &S,
) -> Result<AffineRepairResult, SilenceReason>
where
    C: RingCoeff,
    S: Fn(&[Vec<C>], &[C], usize) -> LinearSolveResult<C>,
{
    let var_idx: BTreeMap<&str, usize> = spec
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
    let dm = ext.kernel_dim();
    let z = ext.r_prime().zero_coeff.zero_like();

    if aff.finite_displacement {
        return compute_finite_affine_repair_generic(
            aff,
            &allowed_indices,
            law_polys,
            ext,
            ambient_lift_rp,
            param_vals_rp,
            solve,
        );
    }

    let num_cols = allowed_indices.len() * dm;
    let num_rows = complex.dim1();
    let mut sub_d0 = vec![vec![z.clone(); num_cols]; num_rows];
    for (row, dst_row) in sub_d0.iter_mut().enumerate().take(num_rows) {
        for (c_block, &v_idx) in allowed_indices.iter().enumerate() {
            for k in 0..dm {
                dst_row[c_block * dm + k] = complex.d0()[row][v_idx * dm + k].clone();
            }
        }
    }
    let neg_res: Vec<C> = residual_m.iter().map(RingCoeff::neg_ref).collect();

    match solve(&sub_d0, &neg_res, num_cols).map_err(map_lift_algebra_error)? {
        Some((particular, kernel_basis)) => {
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
            let particular_map = format_subset_m_map(&aff.allowed_vars, &particular, ext);
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

fn compute_finite_affine_repair_generic<C, S>(
    aff: &AffineAllowedSpec,
    allowed_indices: &[usize],
    law_polys: &[Poly<C>],
    ext: &SquareZeroExtension<C>,
    ambient_lift_rp: &[Vec<C>],
    param_vals_rp: &[Vec<C>],
    solve: &S,
) -> Result<AffineRepairResult, SilenceReason>
where
    C: RingCoeff,
    S: Fn(&[Vec<C>], &[C], usize) -> LinearSolveResult<C>,
{
    let dp = ext.r_prime().dim();
    let z = ext.r_prime().zero_coeff.zero_like();
    let full_base = concat_vecs(ambient_lift_rp, param_vals_rp);

    for poly in law_polys {
        for mono in poly.terms().keys() {
            let deg_allowed: u32 = allowed_indices.iter().map(|&idx| mono.exps()[idx]).sum();
            if deg_allowed > 1 {
                return Err(SilenceReason::SyzygyOutOfScope {
                    detail: "finite_displacement affine repair requires laws affine in allowed_vars"
                        .to_owned(),
                });
            }
        }
    }

    let num_cols = allowed_indices.len() * dp;
    let num_rows = law_polys.len() * dp;
    let mut mat = vec![vec![z; num_cols]; num_rows];
    let mut rhs = Vec::with_capacity(num_rows);

    for (i, poly) in law_polys.iter().enumerate() {
        let res_rp = ext
            .r_prime()
            .eval_poly(poly, &full_base)
            .map_err(map_lift_algebra_error)?;
        rhs.extend(ext.r_prime().neg(&res_rp));
        for (c_block, &v_idx) in allowed_indices.iter().enumerate() {
            let deriv = poly
                .partial_derivative(v_idx)
                .map_err(map_lift_algebra_error)?;
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

    match solve(&mat, &rhs, num_cols).map_err(map_lift_algebra_error)? {
        Some((particular, kernel_basis)) => {
            let shifted =
                apply_rp_subset_shift(ambient_lift_rp, allowed_indices, dp, &particular, ext);
            let mut reeval = reevaluate_laws_in_rp(law_polys, &shifted, param_vals_rp, ext)
                .map_err(map_lift_algebra_error)?;
            let particular_map = format_subset_rp_map(&aff.allowed_vars, &particular, dp, ext);
            let mut torsor_maps = Vec::with_capacity(kernel_basis.len());
            for kb in &kernel_basis {
                let shifted_k = apply_rp_subset_shift(&shifted, allowed_indices, dp, kb, ext);
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
