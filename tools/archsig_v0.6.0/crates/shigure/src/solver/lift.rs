//! 全 syzygy 平方零 lift 複体 $D$（体係数および共通ヘルパ）・入口ディスパッチ（G-141 E1–E8・C8–C9）。

use crate::algebra::MonomialOrder;
use crate::algebra::artin::{AffineSolutionField, FiniteAlgebra, solve_affine_field};
use crate::algebra::artin_quotient::SquareZeroExtension;
use crate::algebra::cochain::CochainComplex;
use crate::algebra::poly::{AlgebraError, Poly};
use crate::algebra::poly_expr::{ExprBindings, VarOrder};
use crate::algebra::scalar::{FpElem, Rat, RingCoeff};
use crate::algebra::syzygy::{
    DEFAULT_MAX_SYZYGY_PAIRS, FieldCoeff, compute_syzygies_field, jacobian_polys,
};
use crate::ir::change::PointDomain;
use crate::ir::lift::{CheckedLiftTask, LiftTaskSpec, SquareZeroSpec};
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{ApplicabilityCheck, ReevalCheck, ShigureOutcome, SilenceReason};
use crate::ir::result_phase4::{LiftOutcomeDetail, RedundantComparisonResult};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::solver::lift_common::{
    apply_m_shift, concat_vecs, conv_cube, conv_mat, conv_vec, derive_lift_verdict,
    eval_ring_params_generic, eval_var_coords_generic, expand_named_polys, format_algebra_label,
    format_m_tuple, format_var_map, lift_outcome, lift_undetermined, lit_to_fp, lit_to_q,
    map_lift_algebra_error, r_action_matrix_field, reevaluate_laws_in_rp, verify_base_laws,
    write_block, compute_etale_descent,
};
use crate::solver::lift_extensions::{
    compute_affine_repair_field, compute_declaration_cover_field,
    compute_raw_cech_field, compute_relative_cone_field,
};
use crate::solver::lift_z::solve_lift_z;
use std::collections::{BTreeMap, BTreeSet};

/// `shigure_lift` の計算核入口（G-141 E1–E8・C8–C9）。
pub fn solve_lift_task(task: &CheckedLiftTask) -> ShigureOutcome {
    let spec = task.spec();
    let coeff_domain = spec.coeff_domain.clone();
    let point_domain = PointDomain::UniversalRing;
    let provenance = build_lift_provenance(spec);
    let mut checks = Vec::new();

    let missing = collect_lift_unobserved(spec);
    if !missing.is_empty() {
        checks.push(ApplicabilityCheck::failed(
            "unobserved_slots_absent",
            MathClause::G140P0Dot1,
            format!("missing slots: {}", missing.join(", ")),
        ));
        return lift_undetermined(
            coeff_domain,
            point_domain,
            checks,
            provenance,
            SilenceReason::UnobservedDependency { slots: missing },
        );
    }
    checks.push(ApplicabilityCheck::passed(
        "unobserved_slots_absent",
        MathClause::G140P0Dot1,
    ));

    match &spec.coeff_domain {
        CoeffDomain::Q => solve_lift_field(
            spec,
            Rat::zero(),
            "Q".to_owned(),
            &|e, b| Poly::from_expr_q(e, b),
            &lit_to_q,
            checks,
            provenance,
        ),
        CoeffDomain::Fp(p) => {
            let Some(zero_fp) = FpElem::zero(p.clone()) else {
                return lift_undetermined(
                    coeff_domain.clone(),
                    point_domain,
                    checks,
                    provenance,
                    SilenceReason::UnsupportedCoeffRing {
                        domain: coeff_domain,
                        detail: format!("modulus {p} is not prime"),
                    },
                );
            };
            let p1 = p.clone();
            let p2 = p.clone();
            solve_lift_field(
                spec,
                zero_fp,
                format!("F_{p}"),
                &move |e, b| Poly::from_expr_fp(e, b, &p1),
                &move |lit| lit_to_fp(lit, &p2),
                checks,
                provenance,
            )
        }
        CoeffDomain::Z => solve_lift_z(spec, checks, provenance),
    }
}

pub(crate) struct CoreLiftField<C: FieldCoeff> {
    pub(crate) syz_gens_str: Vec<Vec<String>>,
    pub(crate) syzygy_identity_verified: bool,
    pub(crate) complex: CochainComplex<C>,
    pub(crate) residual_m: Vec<C>,
    pub(crate) residual_in_m_str: Vec<String>,
    pub(crate) residual_cocycle_verified: bool,
    pub(crate) h0_dim: usize,
    pub(crate) h1_dim: usize,
    pub(crate) h0_basis_str: Vec<Vec<String>>,
    pub(crate) obstruction_class_coords: Vec<String>,
    pub(crate) obstruction_is_zero: bool,
    pub(crate) lift_exists: bool,
    pub(crate) restored_lift: Option<BTreeMap<String, String>>,
    pub(crate) reevaluation: Option<ReevalCheck>,
}

#[allow(clippy::too_many_arguments)]
fn solve_lift_field<C, FE, FL>(
    spec: &LiftTaskSpec,
    zero_coeff: C,
    coeff_label: String,
    expand_expr: &FE,
    lit_conv: &FL,
    mut checks: Vec<ApplicabilityCheck>,
    provenance: Provenance,
) -> ShigureOutcome
where
    C: FieldCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
    FL: Fn(&ScalarLit) -> Result<C, AlgebraError>,
{
    let coeff_domain = spec.coeff_domain.clone();
    let point_domain = PointDomain::UniversalRing;

    let ext = match build_extension_field(&spec.extension, zero_coeff, lit_conv) {
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

    let law_polys = match expand_named_polys(&spec.laws, &bindings, expand_expr) {
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
    let param_vals_rp = match eval_ring_params_generic(spec, expand_expr) {
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
    let param_vals_r: Vec<Vec<C>> = param_vals_rp.iter().map(|v| ext.project(v)).collect();
    let base_pt_r = match eval_var_coords_generic(&spec.variables, &spec.base_point, expand_expr) {
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

    let ambient_lift_rp = match resolve_ambient_lift_field(spec, &ext, &base_pt_r, expand_expr) {
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

    let max_pairs = spec.max_syzygy_pairs.unwrap_or(DEFAULT_MAX_SYZYGY_PAIRS);
    let core = match run_core_lift_field(
        &spec.variables,
        &law_polys,
        &vars,
        &ext,
        &base_pt_r,
        &param_vals_r,
        &ambient_lift_rp,
        &param_vals_rp,
        max_pairs,
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

    let raw_cech_comparison = match compute_raw_cech_field(&core.complex, core.h1_dim) {
        Ok(r) => Some(r),
        Err(reason) => {
            return lift_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };

    let relative_cone = if let Some(rel_spec) = &spec.relative_reading {
        match compute_relative_cone_field(
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
            expand_expr,
            max_pairs,
        ) {
            Ok(rc) => Some(rc),
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
        match compute_declaration_cover_field(
            spec,
            cov_spec,
            &law_polys,
            &ext,
            &base_pt_r,
            &param_vals_r,
            &ambient_lift_rp,
            &param_vals_rp,
            relative_cone.as_ref(),
            expand_expr,
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
        match compute_affine_repair_field(
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
        let ref_polys = match expand_named_polys(&red_spec.reference_laws, &bindings, expand_expr) {
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
        match run_core_lift_field(
            &spec.variables,
            &ref_polys,
            &vars,
            &ext,
            &base_pt_r,
            &param_vals_r,
            &ambient_lift_rp,
            &param_vals_rp,
            max_pairs,
        ) {
            Ok(ref_core) => Some(RedundantComparisonResult {
                ref_h0_dim: ref_core.h0_dim,
                ref_h1_dim: ref_core.h1_dim,
                ref_obstruction_is_zero: ref_core.obstruction_is_zero,
                h0_matches: core.h0_dim == ref_core.h0_dim,
                h1_matches: core.h1_dim == ref_core.h1_dim,
                obstruction_matches: core.obstruction_is_zero == ref_core.obstruction_is_zero,
            }),
            Err(reason) => {
                return lift_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        }
    } else {
        None
    };

    let etale_descent = spec
        .etale_descent
        .as_ref()
        .map(|et| compute_etale_descent(et, &spec.coeff_domain));

    let verdict = derive_lift_verdict(
        core.lift_exists,
        relative_cone.as_ref().map(|r| r.relative_lift_exists),
        affine_repair.as_ref().map(|a| a.repair_exists),
        etale_descent
            .as_ref()
            .map(|e| e.global_regular_section_exists),
    );

    let detail = LiftOutcomeDetail {
        coeff_ring_label: coeff_label,
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
        relative_cone,
        declaration_cover,
        affine_repair,
        redundant_comparison,
        etale_descent,
    };

    lift_outcome(verdict, coeff_domain, point_domain, checks, provenance, detail)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn run_core_lift_field<C: FieldCoeff>(
    variables: &[String],
    law_polys: &[Poly<C>],
    vars: &VarOrder,
    ext: &SquareZeroExtension<C>,
    base_pt_r: &[Vec<C>],
    param_vals_r: &[Vec<C>],
    ambient_lift_rp: &[Vec<C>],
    param_vals_rp: &[Vec<C>],
    max_pairs: usize,
) -> Result<CoreLiftField<C>, SilenceReason> {
    let n = variables.len();
    let r = law_polys.len();
    let dm = ext.kernel_dim();
    let z = ext.r_prime().zero_coeff.zero_like();

    let syz_res = compute_syzygies_field(law_polys, vars.clone(), MonomialOrder::Grevlex, max_pairs)
        .map_err(|e| SilenceReason::SyzygyOutOfScope {
            detail: e.to_string(),
        })?;
    if !syz_res.verified || !syz_res.generating_certified {
        return Err(SilenceReason::SyzygyOutOfScope {
            detail: "syzygy generating certification failed".to_owned(),
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
            let block = r_action_matrix_field(ext, &val_r).map_err(map_lift_algebra_error)?;
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
            let block = r_action_matrix_field(ext, &val_r).map_err(map_lift_algebra_error)?;
            write_block(&mut d1, k * dm, i * dm, &block);
        }
    }

    let complex = CochainComplex::new(n * dm, r * dm, q * dm, d0, d1, z)
        .map_err(map_lift_algebra_error)?;

    let lift_full_rp = concat_vecs(ambient_lift_rp, param_vals_rp);
    let mut residual_m = Vec::with_capacity(r * dm);
    let mut residual_in_m_str = Vec::with_capacity(r);
    for poly in law_polys {
        let val_rp = ext
            .r_prime()
            .eval_poly(poly, &lift_full_rp)
            .map_err(map_lift_algebra_error)?;
        let coords = ext
            .extract_kernel_coords_field(&val_rp)
            .map_err(map_lift_algebra_error)?;
        residual_in_m_str.push(ext.r_prime().format_elem(&val_rp));
        residual_m.extend(coords);
    }

    let coh = complex.cohomology_field().map_err(map_lift_algebra_error)?;
    let coc = complex
        .check_h1_cocycle_field(&coh, &residual_m)
        .map_err(map_lift_algebra_error)?;
    if !coc.is_cocycle {
        return Err(SilenceReason::SyzygyOutOfScope {
            detail: "evaluated residual failed d^1(r) = 0 cocycle verification".to_owned(),
        });
    }

    let h0_basis_str = coh
        .h0_basis
        .iter()
        .map(|b| format_m_tuple(ext, b, n))
        .collect();
    let obstruction_class_coords = coc.class_coords.iter().map(ToString::to_string).collect();
    let obstruction_is_zero = coc.is_zero_class;

    let (restored_lift, reevaluation) = if let Some(witness_pos) = coc.coboundary_witness {
        let delta: Vec<C> = witness_pos.iter().map(RingCoeff::neg_ref).collect();
        let shifted = apply_m_shift(ext, ambient_lift_rp, &delta).map_err(map_lift_algebra_error)?;
        let reeval = reevaluate_laws_in_rp(law_polys, &shifted, param_vals_rp, ext)
            .map_err(map_lift_algebra_error)?;
        (Some(format_var_map(variables, &shifted, ext.r_prime())), Some(reeval))
    } else {
        (None, None)
    };

    Ok(CoreLiftField {
        syz_gens_str,
        syzygy_identity_verified: syz_res.verified,
        complex,
        residual_m,
        residual_in_m_str,
        residual_cocycle_verified: coc.is_cocycle,
        h0_dim: coh.h0_dim,
        h1_dim: coh.h1_dim,
        h0_basis_str,
        obstruction_class_coords,
        obstruction_is_zero,
        lift_exists: obstruction_is_zero,
        restored_lift,
        reevaluation,
    })
}

// =========================================================================
// 共通補助関数（lift_z・lift_extensions・artin からも共用）
// =========================================================================


fn resolve_ambient_lift_field<C, FE>(
    spec: &LiftTaskSpec,
    ext: &SquareZeroExtension<C>,
    base_pt_r: &[Vec<C>],
    expand_expr: &FE,
) -> Result<Vec<Vec<C>>, SilenceReason>
where
    C: FieldCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
{
    if let Some(lift_spec) = &spec.ambient_lift {
        let vals = eval_var_coords_generic(&spec.variables, lift_spec, expand_expr)
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
    let z = ext.r_prime().zero_coeff.zero_like();
    let mut out = Vec::with_capacity(base_pt_r.len());
    for b in base_pt_r {
        match solve_affine_field(ext.projection(), b, ext.r_prime().dim(), &z)
            .map_err(map_lift_algebra_error)?
        {
            AffineSolutionField::Consistent { particular, .. } => out.push(particular),
            AffineSolutionField::Inconsistent { .. } => {
                return Err(SilenceReason::SquareZeroConditionViolated {
                    detail: "projection R' -> R failed to lift base_point".to_owned(),
                });
            }
        }
    }
    Ok(out)
}

fn build_extension_field<C, FL>(
    spec: &SquareZeroSpec,
    zero_coeff: C,
    lit_conv: &FL,
) -> Result<SquareZeroExtension<C>, AlgebraError>
where
    C: FieldCoeff,
    FL: Fn(&ScalarLit) -> Result<C, AlgebraError>,
{
    match spec {
        SquareZeroSpec::TruncatedPoly {
            var_name,
            base_degree,
        } => SquareZeroExtension::truncated_step_field(var_name, *base_degree, zero_coeff),
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
                zero_coeff: zero_coeff.zero_like(),
                one: conv_vec(r_prime_one, lit_conv)?,
                mul_table: conv_cube(r_prime_mul, lit_conv)?,
            };
            let rb = FiniteAlgebra {
                basis_names: r_base_basis.clone(),
                zero_coeff: zero_coeff.zero_like(),
                one: conv_vec(r_base_one, lit_conv)?,
                mul_table: conv_cube(r_base_mul, lit_conv)?,
            };
            SquareZeroExtension::new_field(rp, rb, conv_mat(projection, lit_conv)?)
        }
    }
}


fn build_lift_provenance(spec: &LiftTaskSpec) -> Provenance {
    let mut clauses = spec.provenance.clauses.clone();
    for c in [MathClause::G141E1, MathClause::G141E2, MathClause::G141E4, MathClause::G141E8] {
        if !clauses.contains(&c) {
            clauses.push(c);
        }
    }
    if spec.relative_reading.is_some() && !clauses.contains(&MathClause::G141E5) {
        clauses.push(MathClause::G141E5);
    }
    if spec.affine_allowed.is_some() && !clauses.contains(&MathClause::G141E6) {
        clauses.push(MathClause::G141E6);
    }
    if spec.declaration_cover.is_some() && !clauses.contains(&MathClause::G141E7) {
        clauses.push(MathClause::G141E7);
    }
    if spec.etale_descent.is_some() && !clauses.contains(&MathClause::G141C9) {
        clauses.push(MathClause::G141C9);
    }
    Provenance::new(spec.provenance.origins.clone(), clauses)
}

fn collect_lift_unobserved(spec: &LiftTaskSpec) -> Vec<String> {
    let mut slots = BTreeSet::new();
    for rp in &spec.ring_params {
        for e in &rp.value_in_r_prime {
            e.collect_unobserved(&mut slots);
        }
    }
    for law in &spec.laws {
        law.expr.collect_unobserved(&mut slots);
    }
    for (_, coords) in &spec.base_point {
        for e in coords {
            e.collect_unobserved(&mut slots);
        }
    }
    if let Some(lift) = &spec.ambient_lift {
        for (_, coords) in lift {
            for e in coords {
                e.collect_unobserved(&mut slots);
            }
        }
    }
    if let Some(rel) = &spec.relative_reading {
        for ol in &rel.obs_laws {
            ol.expr.collect_unobserved(&mut slots);
        }
        for (_, e) in &rel.reading_map {
            e.collect_unobserved(&mut slots);
        }
        for (_, coords) in &rel.designated_obs_lift {
            for e in coords {
                e.collect_unobserved(&mut slots);
            }
        }
        if let Some(rr) = &rel.raw_read_diff {
            rr.expr.collect_unobserved(&mut slots);
        }
    }
    if let Some(cov) = &spec.declaration_cover {
        for c in &cov.contexts {
            for obs in &c.observations {
                obs.expr.collect_unobserved(&mut slots);
            }
        }
    }
    if let Some(red) = &spec.redundant_comparison {
        for rl in &red.reference_laws {
            rl.expr.collect_unobserved(&mut slots);
        }
    }
    slots.into_iter().collect()
}

