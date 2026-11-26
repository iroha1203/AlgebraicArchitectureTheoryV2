//! 整数環 $\mathbb{Z}$ 上の全 syzygy 平方零 lift 計算核（H2 $(z^2, 2z^2)$・相対 cone・アフィン修復）。

use crate::algebra::MonomialOrder;
use crate::algebra::artin::FiniteAlgebra;
use crate::algebra::artin_quotient::SquareZeroExtension;
use crate::algebra::cochain::CochainComplex;
use crate::algebra::linear::{AffineSolutionZ, solve_affine_z};
use crate::algebra::poly::{AlgebraError, Poly};
use crate::algebra::poly_expr::{ExprBindings, VarOrder};
use crate::algebra::syzygy::{compute_syzygies_z, jacobian_polys};
use crate::ir::change::PointDomain;
use crate::ir::lift::{LiftTaskSpec, SquareZeroSpec};
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{ApplicabilityCheck, ReevalCheck, ShigureOutcome, SilenceReason};
use crate::ir::result_phase4::{LiftOutcomeDetail, RedundantComparisonResult};
use crate::ir::term::CoeffDomain;
use crate::solver::lift_affine::compute_affine_repair_z;
use crate::solver::lift_common::{
    apply_m_shift, compute_etale_descent, concat_vecs, conv_cube, conv_mat, conv_vec,
    derive_lift_verdict, eval_ring_params_generic, eval_var_coords_generic, expand_named_polys,
    format_algebra_label, format_m_tuple, format_var_map, lift_outcome, lift_undetermined,
    lit_to_z, map_lift_algebra_error, reevaluate_laws_in_rp, verify_base_laws, write_block,
};
use crate::solver::lift_z_ext::{
    compute_declaration_cover_z, compute_raw_cech_z, compute_relative_cone_z, r_action_matrix_z,
};
use num_bigint::BigInt;
use num_traits::Zero;
use std::collections::BTreeMap;

pub(crate) struct CoreLiftZ {
    syz_gens_str: Vec<Vec<String>>,
    syzygy_identity_verified: bool,
    pub(crate) complex: CochainComplex<BigInt>,
    pub(crate) residual_m: Vec<BigInt>,
    residual_in_m_str: Vec<String>,
    residual_cocycle_verified: bool,
    h0_dim: usize,
    h0_torsion: Vec<BigInt>,
    h1_dim: usize,
    h1_torsion: Vec<BigInt>,
    h0_basis_str: Vec<Vec<String>>,
    obstruction_class_coords: Vec<String>,
    obstruction_is_zero: bool,
    lift_exists: bool,
    restored_lift: Option<BTreeMap<String, String>>,
    reevaluation: Option<ReevalCheck>,
}

pub(crate) fn solve_lift_z(
    spec: &LiftTaskSpec,
    mut checks: Vec<ApplicabilityCheck>,
    provenance: Provenance,
) -> ShigureOutcome {
    let coeff_domain = CoeffDomain::Z;
    let point_domain = PointDomain::UniversalRing;

    let ext = match build_extension_z(&spec.extension) {
        Ok(ext) => {
            checks.push(ApplicabilityCheck::passed(
                "square_zero_extension_valid",
                MathClause::G141E1,
            ));
            ext
        }
        Err(e) => {
            checks.push(ApplicabilityCheck::failed(
                "square_zero_extension_valid",
                MathClause::G141E1,
                e.to_string(),
            ));
            return lift_undetermined(
                coeff_domain,
                point_domain,
                checks,
                provenance,
                SilenceReason::SquareZeroConditionViolated {
                    detail: e.to_string(),
                },
            );
        }
    };

    let param_names: Vec<String> = spec.ring_params.iter().map(|p| p.name.clone()).collect();
    let (vars, bindings) = match ExprBindings::from_slices(&spec.variables, &[], &param_names) {
        Ok(pair) => pair,
        Err(e) => {
            return lift_undetermined(
                coeff_domain,
                point_domain,
                checks,
                provenance,
                map_lift_algebra_error(e),
            );
        }
    };

    let law_polys = match expand_named_polys(&spec.laws, &bindings, &Poly::from_expr_z) {
        Ok(v) => v,
        Err(e) => {
            return lift_undetermined(
                coeff_domain,
                point_domain,
                checks,
                provenance,
                map_lift_algebra_error(e),
            );
        }
    };
    let param_vals_rp = match eval_ring_params_generic(spec, &Poly::from_expr_z) {
        Ok(v) => v,
        Err(e) => {
            return lift_undetermined(
                coeff_domain,
                point_domain,
                checks,
                provenance,
                map_lift_algebra_error(e),
            );
        }
    };
    let param_vals_r: Vec<Vec<BigInt>> = param_vals_rp.iter().map(|v| ext.project(v)).collect();
    let base_pt_r =
        match eval_var_coords_generic(&spec.variables, &spec.base_point, &Poly::from_expr_z) {
            Ok(v) => v,
            Err(e) => {
                return lift_undetermined(
                    coeff_domain,
                    point_domain,
                    checks,
                    provenance,
                    map_lift_algebra_error(e),
                );
            }
        };

    if let Err(reason) = verify_base_laws(&spec.laws, &law_polys, &base_pt_r, &param_vals_r, &ext) {
        checks.push(ApplicabilityCheck::failed(
            "base_point_satisfies_laws_in_R",
            MathClause::G141E1,
            reason.code(),
        ));
        return lift_undetermined(coeff_domain, point_domain, checks, provenance, reason);
    }
    checks.push(ApplicabilityCheck::passed(
        "base_point_satisfies_laws_in_R",
        MathClause::G141E1,
    ));

    let ambient_lift_rp = match resolve_ambient_lift_z(spec, &ext, &base_pt_r) {
        Ok(v) => v,
        Err(reason) => {
            checks.push(ApplicabilityCheck::failed(
                "ambient_lift_projects_to_base_point",
                MathClause::G141E1,
                reason.code(),
            ));
            return lift_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };
    checks.push(ApplicabilityCheck::passed(
        "ambient_lift_projects_to_base_point",
        MathClause::G141E1,
    ));

    let core = match run_core_lift_z(
        &spec.variables,
        &law_polys,
        &vars,
        &ext,
        &base_pt_r,
        &param_vals_r,
        &ambient_lift_rp,
        &param_vals_rp,
    ) {
        Ok(c) => c,
        Err(reason) => {
            checks.push(ApplicabilityCheck::failed(
                "full_syzygy_complex_computed",
                MathClause::G141E2,
                reason.code(),
            ));
            return lift_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };
    checks.push(ApplicabilityCheck::passed(
        "full_syzygy_complex_computed",
        MathClause::G141E2,
    ));

    let raw_cech_comparison = match compute_raw_cech_z(&core.complex, core.h1_dim) {
        Ok(r) => Some(r),
        Err(reason) => {
            return lift_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };

    let mut relative_cone = if let Some(rel_spec) = &spec.relative_reading {
        match compute_relative_cone_z(
            spec,
            rel_spec,
            &law_polys,
            &vars,
            &bindings,
            &ext,
            &base_pt_r,
            &param_vals_r,
            &ambient_lift_rp,
            &param_vals_rp,
            &core,
        ) {
            Ok(rc) => {
                checks.push(ApplicabilityCheck::passed(
                    "relative_reading_cone_computed",
                    MathClause::G141E5,
                ));
                Some(rc)
            }
            Err(reason) => {
                checks.push(ApplicabilityCheck::failed(
                    "relative_reading_cone_computed",
                    MathClause::G141E5,
                    reason.code(),
                ));
                return lift_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        }
    } else {
        None
    };

    let declaration_cover = if let Some(cov_spec) = &spec.declaration_cover {
        match compute_declaration_cover_z(
            spec,
            cov_spec,
            &law_polys,
            &ext,
            &base_pt_r,
            &param_vals_r,
            &ambient_lift_rp,
            &param_vals_rp,
            &core,
            relative_cone.as_mut(),
        ) {
            Ok(dc) => Some(dc),
            Err(reason) => {
                return lift_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        }
    } else {
        None
    };

    let affine_repair = if let Some(aff_spec) = &spec.affine_allowed {
        match compute_affine_repair_z(
            spec,
            aff_spec,
            &law_polys,
            &ext,
            &ambient_lift_rp,
            &param_vals_rp,
            &core,
        ) {
            Ok(ar) => Some(ar),
            Err(reason) => {
                return lift_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        }
    } else {
        None
    };

    let redundant_comparison = if let Some(red_spec) = &spec.redundant_comparison {
        let ref_polys =
            match expand_named_polys(&red_spec.reference_laws, &bindings, &Poly::from_expr_z) {
                Ok(v) => v,
                Err(e) => {
                    return lift_undetermined(
                        coeff_domain,
                        point_domain,
                        checks,
                        provenance,
                        map_lift_algebra_error(e),
                    );
                }
            };
        if let Err(reason) = verify_base_laws(
            &red_spec.reference_laws,
            &ref_polys,
            &base_pt_r,
            &param_vals_r,
            &ext,
        ) {
            checks.push(ApplicabilityCheck::failed(
                "reference_laws_satisfied_at_base_point",
                MathClause::G141E2,
                reason.code(),
            ));
            return lift_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
        match run_core_lift_z(
            &spec.variables,
            &ref_polys,
            &vars,
            &ext,
            &base_pt_r,
            &param_vals_r,
            &ambient_lift_rp,
            &param_vals_rp,
        ) {
            Ok(ref_core) => Some(RedundantComparisonResult {
                ref_h0_dim: ref_core.h0_dim,
                ref_h1_dim: ref_core.h1_dim,
                ref_obstruction_is_zero: ref_core.obstruction_is_zero,
                h0_matches: core.h0_dim == ref_core.h0_dim
                    && core.h0_torsion == ref_core.h0_torsion,
                h1_matches: core.h1_dim == ref_core.h1_dim
                    && core.h1_torsion == ref_core.h1_torsion,
                obstruction_matches: core.obstruction_is_zero == ref_core.obstruction_is_zero,
            }),
            Err(reason) => {
                return lift_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        }
    } else {
        None
    };

    let etale_descent = if let Some(et) = &spec.etale_descent {
        match compute_etale_descent(et, &spec.coeff_domain) {
            Ok(res) => {
                checks.push(ApplicabilityCheck::passed(
                    "finite_etale_cover_applicable",
                    MathClause::G141C9,
                ));
                Some(res)
            }
            Err(reason) => {
                checks.push(ApplicabilityCheck::failed(
                    "finite_etale_cover_applicable",
                    MathClause::G141C9,
                    reason.code(),
                ));
                return lift_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        }
    } else {
        None
    };

    let relative_cone_result = relative_cone.map(|rc| rc.result);
    let verdict = derive_lift_verdict(
        core.lift_exists,
        relative_cone_result
            .as_ref()
            .map(|r| r.relative_lift_exists),
        affine_repair.as_ref().map(|a| a.repair_exists),
        etale_descent
            .as_ref()
            .map(|e| e.global_regular_section_exists),
    );

    let detail = LiftOutcomeDetail {
        coeff_ring_label: "Z".to_owned(),
        r_base_label: format_algebra_label(&spec.extension, false),
        r_prime_label: format_algebra_label(&spec.extension, true),
        kernel_dim: ext.kernel_dim(),
        square_zero_verified: ext.square_zero_verified(),
        base_point_lawful: true,
        syzygy_generators: core.syz_gens_str,
        syzygy_identity_verified: core.syzygy_identity_verified,
        complex_d1_d0_zero_verified: true,
        residual_cocycle_verified: core.residual_cocycle_verified,
        residual_in_m: core.residual_in_m_str,
        h0_dim: core.h0_dim,
        h1_dim: core.h1_dim,
        h0_basis: core.h0_basis_str,
        obstruction_class_coords: core.obstruction_class_coords,
        obstruction_is_zero: core.obstruction_is_zero,
        lift_exists: core.lift_exists,
        restored_lift: core.restored_lift,
        reevaluation: core.reevaluation,
        raw_cech_comparison,
        relative_cone: relative_cone_result,
        declaration_cover,
        affine_repair,
        redundant_comparison,
        etale_descent,
    };

    lift_outcome(
        verdict,
        coeff_domain,
        point_domain,
        checks,
        provenance,
        detail,
    )
}

#[allow(clippy::too_many_arguments)]
fn run_core_lift_z(
    variables: &[String],
    law_polys: &[Poly<BigInt>],
    vars: &VarOrder,
    ext: &SquareZeroExtension<BigInt>,
    base_pt_r: &[Vec<BigInt>],
    param_vals_r: &[Vec<BigInt>],
    ambient_lift_rp: &[Vec<BigInt>],
    param_vals_rp: &[Vec<BigInt>],
) -> Result<CoreLiftZ, SilenceReason> {
    let n = variables.len();
    let r = law_polys.len();
    let dm = ext.kernel_dim();
    let z = BigInt::zero();

    let syz_res = compute_syzygies_z(law_polys, vars.clone()).map_err(|e| {
        SilenceReason::SyzygyOutOfScope {
            detail: e.to_string(),
        }
    })?;
    if !syz_res.verified || !syz_res.generating_certified {
        return Err(SilenceReason::SyzygyOutOfScope {
            detail: "Z syzygy generating certification failed".to_owned(),
        });
    }
    let q = syz_res.generators.len();
    let syz_gens_str: Vec<Vec<String>> = syz_res
        .generators
        .iter()
        .map(|s| {
            s.iter()
                .map(|p| p.display(vars, MonomialOrder::Grevlex))
                .collect()
        })
        .collect();

    let jac = jacobian_polys(law_polys, vars.len()).map_err(map_lift_algebra_error)?;
    let base_full_r = concat_vecs(base_pt_r, param_vals_r);

    let mut d0 = vec![vec![z.clone(); n * dm]; r * dm];
    for (i, jac_row) in jac.iter().enumerate().take(r) {
        for (j, jac_entry) in jac_row.iter().enumerate().take(n) {
            let val_r = ext
                .r_base()
                .eval_poly(jac_entry, &base_full_r)
                .map_err(map_lift_algebra_error)?;
            let block = r_action_matrix_z(ext, &val_r).map_err(map_lift_algebra_error)?;
            write_block(&mut d0, i * dm, j * dm, &block);
        }
    }

    let mut d1 = vec![vec![z.clone(); r * dm]; q * dm];
    for (k, syz) in syz_res.generators.iter().enumerate() {
        for (i, poly) in syz.iter().enumerate() {
            let val_r = ext
                .r_base()
                .eval_poly(poly, &base_full_r)
                .map_err(map_lift_algebra_error)?;
            let block = r_action_matrix_z(ext, &val_r).map_err(map_lift_algebra_error)?;
            write_block(&mut d1, k * dm, i * dm, &block);
        }
    }

    let complex =
        CochainComplex::new(n * dm, r * dm, q * dm, d0, d1, z).map_err(map_lift_algebra_error)?;

    let lift_full_rp = concat_vecs(ambient_lift_rp, param_vals_rp);
    let mut residual_m = Vec::with_capacity(r * dm);
    let mut residual_in_m_str = Vec::with_capacity(r);
    for poly in law_polys {
        let val_rp = ext
            .r_prime()
            .eval_poly(poly, &lift_full_rp)
            .map_err(map_lift_algebra_error)?;
        let coords = ext
            .extract_kernel_coords_z(&val_rp)
            .map_err(map_lift_algebra_error)?;
        residual_in_m_str.push(ext.r_prime().format_elem(&val_rp));
        residual_m.extend(coords);
    }

    let coh = complex.cohomology_z().map_err(map_lift_algebra_error)?;
    let coc = complex
        .check_h1_cocycle_z(&residual_m)
        .map_err(map_lift_algebra_error)?;
    if !coc.is_cocycle {
        return Err(SilenceReason::SyzygyOutOfScope {
            detail: "evaluated Z residual failed d^1(r) = 0 cocycle verification".to_owned(),
        });
    }

    let h0_basis_str = coh
        .h0_basis
        .iter()
        .map(|b| format_m_tuple(ext, b, n))
        .collect();
    let obstruction_is_zero = coc.is_zero_in_z;
    let obstruction_class_coords = if obstruction_is_zero {
        Vec::new()
    } else {
        residual_m.iter().map(ToString::to_string).collect()
    };

    let (restored_lift, reevaluation) = if let Some(witness_pos) = coc.coboundary_witness_z {
        let delta: Vec<BigInt> = witness_pos.iter().map(|v| -v).collect();
        let shifted =
            apply_m_shift(ext, ambient_lift_rp, &delta).map_err(map_lift_algebra_error)?;
        let reeval = reevaluate_laws_in_rp(law_polys, &shifted, param_vals_rp, ext)
            .map_err(map_lift_algebra_error)?;
        (
            Some(format_var_map(variables, &shifted, ext.r_prime())),
            Some(reeval),
        )
    } else {
        (None, None)
    };

    Ok(CoreLiftZ {
        syz_gens_str,
        syzygy_identity_verified: syz_res.verified,
        complex,
        residual_m,
        residual_in_m_str,
        residual_cocycle_verified: coc.is_cocycle,
        h0_dim: coh.h0.free_rank,
        h0_torsion: coh.h0.torsion_invariants,
        h1_dim: coh.h1.free_rank,
        h1_torsion: coh.h1.torsion_invariants,
        h0_basis_str,
        obstruction_class_coords,
        obstruction_is_zero,
        lift_exists: obstruction_is_zero,
        restored_lift,
        reevaluation,
    })
}

fn resolve_ambient_lift_z(
    spec: &LiftTaskSpec,
    ext: &SquareZeroExtension<BigInt>,
    base_pt_r: &[Vec<BigInt>],
) -> Result<Vec<Vec<BigInt>>, SilenceReason> {
    if let Some(lift_spec) = &spec.ambient_lift {
        let vals = eval_var_coords_generic(&spec.variables, lift_spec, &Poly::from_expr_z)
            .map_err(map_lift_algebra_error)?;
        for (i, (l, b)) in vals.iter().zip(base_pt_r).enumerate() {
            if ext.project(l) != *b {
                return Err(SilenceReason::ApplicabilityConditionNotMet {
                    condition: "ambient_lift_projects_to_base_point".to_owned(),
                    detail: format!(
                        "ambient_lift for `{}` does not project to base_point in R",
                        spec.variables[i]
                    ),
                });
            }
        }
        return Ok(vals);
    }
    let mut out = Vec::with_capacity(base_pt_r.len());
    for b in base_pt_r {
        match solve_affine_z(ext.projection(), b, ext.r_prime().dim())
            .map_err(map_lift_algebra_error)?
        {
            AffineSolutionZ::Consistent { particular, .. } => out.push(particular),
            AffineSolutionZ::Inconsistent { .. } => {
                return Err(SilenceReason::SquareZeroConditionViolated {
                    detail: "Z projection R' -> R failed to lift base_point".to_owned(),
                });
            }
        }
    }
    Ok(out)
}

fn build_extension_z(spec: &SquareZeroSpec) -> Result<SquareZeroExtension<BigInt>, AlgebraError> {
    match spec {
        SquareZeroSpec::TruncatedPoly {
            var_name,
            base_degree,
        } => SquareZeroExtension::truncated_step_z(var_name, *base_degree),
        SquareZeroSpec::ExplicitTable {
            r_prime_basis,
            r_prime_one,
            r_prime_mul,
            r_base_basis,
            r_base_one,
            r_base_mul,
            projection,
        } => {
            let rp = FiniteAlgebra {
                basis_names: r_prime_basis.clone(),
                zero_coeff: BigInt::zero(),
                one: conv_vec(r_prime_one, &lit_to_z)?,
                mul_table: conv_cube(r_prime_mul, &lit_to_z)?,
            };
            let rb = FiniteAlgebra {
                basis_names: r_base_basis.clone(),
                zero_coeff: BigInt::zero(),
                one: conv_vec(r_base_one, &lit_to_z)?,
                mul_table: conv_cube(r_base_mul, &lit_to_z)?,
            };
            SquareZeroExtension::new_z(rp, rb, conv_mat(projection, &lit_to_z)?)
        }
    }
}
