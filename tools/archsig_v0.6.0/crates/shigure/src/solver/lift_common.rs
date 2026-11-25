//! `solver/lift`・`solver/lift_z`・`solver/lift_extensions` 間の共通補助関数。

use crate::algebra::MonomialOrder;
use crate::algebra::artin::{AffineSolutionField, FiniteAlgebra, solve_affine_field};
use crate::algebra::artin_quotient::SquareZeroExtension;
use crate::algebra::linear::{AffineSolutionZ, solve_affine_z};
use crate::algebra::poly::{AlgebraError, Poly};
use crate::algebra::poly_expr::{ExprBindings, VarOrder};
use crate::algebra::scalar::{FpElem, Rat, RingCoeff};
use crate::algebra::syzygy::{DEFAULT_MAX_SYZYGY_PAIRS, FieldCoeff, ideal_membership_field};
use crate::ir::change::{NamedPoly, PointDomain};
use crate::ir::lift::{
    DeclarationCoverSpec, FiniteEtaleDescentSpec, LiftTaskSpec, SquareZeroSpec,
};
use crate::ir::provenance::Provenance;
use crate::ir::result::{ApplicabilityCheck, ReevalCheck, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_phase4::{FiniteEtaleDescentResult, LiftOutcomeDetail};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) fn verify_base_laws<C: RingCoeff>(
    laws: &[NamedPoly],
    law_polys: &[Poly<C>],
    base_pt_r: &[Vec<C>],
    param_vals_r: &[Vec<C>],
    ext: &SquareZeroExtension<C>,
) -> Result<(), SilenceReason> {
    let base_full_r = concat_vecs(base_pt_r, param_vals_r);
    for (law, poly) in laws.iter().zip(law_polys) {
        let val = ext
            .r_base()
            .eval_poly(poly, &base_full_r)
            .map_err(map_lift_algebra_error)?;
        if !ext.r_base().is_zero_elem(&val) {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "base_point_satisfies_laws_in_R".to_owned(),
                detail: format!(
                    "law `{}` evaluates to {} != 0 in R",
                    law.name,
                    ext.r_base().format_elem(&val)
                ),
            });
        }
    }
    Ok(())
}

pub(crate) fn r_action_matrix_field<C: FieldCoeff>(
    ext: &SquareZeroExtension<C>,
    a_in_r: &[C],
) -> Result<Vec<Vec<C>>, AlgebraError> {
    let z = ext.r_prime().zero_coeff.zero_like();
    let dm = ext.kernel_dim();
    let a_lift = match solve_affine_field(ext.projection(), a_in_r, ext.r_prime().dim(), &z)? {
        AffineSolutionField::Consistent { particular, .. } => particular,
        AffineSolutionField::Inconsistent { .. } => {
            return Err(AlgebraError::OutOfScope {
                detail: "projection R' -> R is not surjective".to_owned(),
            });
        }
    };
    let mut block = vec![vec![z; dm]; dm];
    for (col, kb) in ext.kernel_basis().iter().enumerate() {
        let prod = ext.r_prime().mul(&a_lift, kb);
        let coords = ext.extract_kernel_coords_field(&prod)?;
        for (row, val) in coords.into_iter().enumerate() {
            block[row][col] = val;
        }
    }
    Ok(block)
}

pub(crate) fn write_block<C: Clone>(
    dst: &mut [Vec<C>],
    row_off: usize,
    col_off: usize,
    block: &[Vec<C>],
) {
    for (r, row) in block.iter().enumerate() {
        for (c, val) in row.iter().enumerate() {
            dst[row_off + r][col_off + c] = val.clone();
        }
    }
}

pub(crate) fn apply_m_shift<C: RingCoeff>(
    ext: &SquareZeroExtension<C>,
    base_rp: &[Vec<C>],
    delta_m: &[C],
) -> Result<Vec<Vec<C>>, AlgebraError> {
    let dm = ext.kernel_dim();
    let mut out = Vec::with_capacity(base_rp.len());
    for (i, elem) in base_rp.iter().enumerate() {
        let slice = &delta_m[i * dm..(i + 1) * dm];
        let emb = ext.embed_kernel(slice)?;
        out.push(ext.r_prime().add(elem, &emb));
    }
    Ok(out)
}

pub(crate) fn reevaluate_laws_in_rp<C: RingCoeff>(
    law_polys: &[Poly<C>],
    var_vals_rp: &[Vec<C>],
    param_vals_rp: &[Vec<C>],
    ext: &SquareZeroExtension<C>,
) -> Result<ReevalCheck, AlgebraError> {
    let full = concat_vecs(var_vals_rp, param_vals_rp);
    let mut bad = Vec::new();
    for (idx, poly) in law_polys.iter().enumerate() {
        let v = ext.r_prime().eval_poly(poly, &full)?;
        if !ext.r_prime().is_zero_elem(&v) {
            bad.push(format!("law[{idx}]={}", ext.r_prime().format_elem(&v)));
        }
    }
    Ok(ReevalCheck {
        checked: true,
        matched: bad.is_empty(),
        detail: if bad.is_empty() {
            format!("all {} primitive laws re-evaluated to 0 in R'", law_polys.len())
        } else {
            format!("nonzero law residuals in R': {}", bad.join(", "))
        },
    })
}

pub(crate) fn format_m_tuple<C: RingCoeff>(
    ext: &SquareZeroExtension<C>,
    vec_m: &[C],
    num_vars: usize,
) -> Vec<String> {
    let dm = ext.kernel_dim();
    (0..num_vars)
        .map(|i| {
            let slice = &vec_m[i * dm..(i + 1) * dm];
            match ext.embed_kernel(slice) {
                Ok(e) => ext.r_prime().format_elem(&e),
                Err(_) => "0".to_owned(),
            }
        })
        .collect()
}

pub(crate) fn format_var_map<C: RingCoeff>(
    names: &[String],
    vals: &[Vec<C>],
    alg: &FiniteAlgebra<C>,
) -> BTreeMap<String, String> {
    names
        .iter()
        .zip(vals)
        .map(|(n, v)| (n.clone(), alg.format_elem(v)))
        .collect()
}

pub(crate) fn concat_vecs<T: Clone>(a: &[T], b: &[T]) -> Vec<T> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    out.extend_from_slice(a);
    out.extend_from_slice(b);
    out
}

pub(crate) fn expand_named_polys<C, FE>(
    items: &[NamedPoly],
    bindings: &ExprBindings,
    expand_expr: &FE,
) -> Result<Vec<Poly<C>>, AlgebraError>
where
    C: RingCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
{
    items
        .iter()
        .map(|item| expand_expr(&item.expr, bindings))
        .collect()
}

pub(crate) fn eval_const_expr<C, FE>(expr: &PolyExpr, expand_expr: &FE) -> Result<C, AlgebraError>
where
    C: RingCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
{
    let (_, empty_b) = ExprBindings::from_slices(&[], &[], &[])?;
    Ok(expand_expr(expr, &empty_b)?.constant_value())
}

pub(crate) fn eval_var_coords_generic<C, FE>(
    var_order: &[String],
    entries: &[(String, Vec<PolyExpr>)],
    expand_expr: &FE,
) -> Result<Vec<Vec<C>>, AlgebraError>
where
    C: RingCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
{
    let map: BTreeMap<&str, &[PolyExpr]> = entries
        .iter()
        .map(|(k, v)| (k.as_str(), v.as_slice()))
        .collect();
    let mut out = Vec::with_capacity(var_order.len());
    for v in var_order {
        let exprs = map.get(v.as_str()).ok_or_else(|| AlgebraError::UnknownVariable {
            name: v.clone(),
        })?;
        let mut coords = Vec::with_capacity(exprs.len());
        for e in *exprs {
            coords.push(eval_const_expr(e, expand_expr)?);
        }
        out.push(coords);
    }
    Ok(out)
}

pub(crate) fn eval_ring_params_generic<C, FE>(
    spec: &LiftTaskSpec,
    expand_expr: &FE,
) -> Result<Vec<Vec<C>>, AlgebraError>
where
    C: RingCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
{
    let mut out = Vec::with_capacity(spec.ring_params.len());
    for rp in &spec.ring_params {
        let mut coords = Vec::with_capacity(rp.value_in_r_prime.len());
        for e in &rp.value_in_r_prime {
            coords.push(eval_const_expr(e, expand_expr)?);
        }
        out.push(coords);
    }
    Ok(out)
}


pub(crate) fn conv_vec<C, FL>(lits: &[ScalarLit], f: &FL) -> Result<Vec<C>, AlgebraError>
where
    FL: Fn(&ScalarLit) -> Result<C, AlgebraError>,
{
    lits.iter().map(f).collect()
}

pub(crate) fn conv_mat<C, FL>(mat: &[Vec<ScalarLit>], f: &FL) -> Result<Vec<Vec<C>>, AlgebraError>
where
    FL: Fn(&ScalarLit) -> Result<C, AlgebraError>,
{
    mat.iter().map(|r| conv_vec(r, f)).collect()
}

pub(crate) fn conv_cube<C, FL>(
    cube: &[Vec<Vec<ScalarLit>>],
    f: &FL,
) -> Result<Vec<Vec<Vec<C>>>, AlgebraError>
where
    FL: Fn(&ScalarLit) -> Result<C, AlgebraError>,
{
    cube.iter().map(|m| conv_mat(m, f)).collect()
}

pub(crate) fn lit_to_q(lit: &ScalarLit) -> Result<Rat, AlgebraError> {
    match lit {
        ScalarLit::Q { num, den } => Rat::new(num.clone(), den.clone()).ok_or_else(|| {
            AlgebraError::OutOfScope {
                detail: "zero denominator in Q literal".to_owned(),
            }
        }),
        ScalarLit::Z(z) => Ok(Rat::from_int(z.clone())),
        other => Err(AlgebraError::DomainMismatch {
            expected: "Q".to_owned(),
            actual: other.domain().to_string(),
        }),
    }
}

pub(crate) fn lit_to_z(lit: &ScalarLit) -> Result<BigInt, AlgebraError> {
    match lit {
        ScalarLit::Z(z) => Ok(z.clone()),
        other => Err(AlgebraError::DomainMismatch {
            expected: "Z".to_owned(),
            actual: other.domain().to_string(),
        }),
    }
}

pub(crate) fn lit_to_fp(lit: &ScalarLit, p: &BigUint) -> Result<FpElem, AlgebraError> {
    match lit {
        ScalarLit::Fp { value, modulus } if modulus == p => Ok(FpElem::from_checked_prime(
            BigInt::from(value.clone()),
            p.clone(),
        )),
        other => Err(AlgebraError::DomainMismatch {
            expected: format!("Fp({p})"),
            actual: other.domain().to_string(),
        }),
    }
}

pub(crate) fn map_lift_algebra_error(err: AlgebraError) -> SilenceReason {
    match err {
        AlgebraError::UnobservedDependency { slots } => SilenceReason::UnobservedDependency { slots },
        AlgebraError::OutOfScope { detail } => SilenceReason::SyzygyOutOfScope { detail },
        other => SilenceReason::ApplicabilityConditionNotMet {
            condition: "lift_algebra_computation".to_owned(),
            detail: other.to_string(),
        },
    }
}

pub(crate) fn derive_lift_verdict(
    lift_exists: bool,
    relative_lift_exists: Option<bool>,
    affine_repair_exists: Option<bool>,
    etale_global_exists: Option<bool>,
) -> Verdict {
    let ok = lift_exists
        && relative_lift_exists.unwrap_or(true)
        && affine_repair_exists.unwrap_or(true)
        && etale_global_exists.unwrap_or(true);
    if ok {
        Verdict::Established
    } else {
        Verdict::Refuted
    }
}

pub(crate) fn format_algebra_label(ext: &SquareZeroSpec, is_prime: bool) -> String {
    match ext {
        SquareZeroSpec::TruncatedPoly {
            var_name,
            base_degree,
        } => {
            let deg = if is_prime {
                base_degree + 2
            } else {
                base_degree + 1
            };
            if deg == 1 {
                "k".to_owned()
            } else {
                format!("k[{var_name}]/({var_name}^{deg})")
            }
        }
        SquareZeroSpec::ExplicitTable {
            r_prime_basis,
            r_base_basis,
            ..
        } => {
            if is_prime {
                format!("explicit(dim={})", r_prime_basis.len())
            } else {
                format!("explicit(dim={})", r_base_basis.len())
            }
        }
    }
}


pub(crate) fn lift_undetermined(
    coeff_domain: CoeffDomain,
    point_domain: PointDomain,
    applicability: Vec<ApplicabilityCheck>,
    provenance: Provenance,
    reason: SilenceReason,
) -> ShigureOutcome {
    ShigureOutcome {
        verdict: Verdict::Undetermined(reason),
        coeff_domain,
        point_domain,
        applicability,
        provenance,
        residual_ideal: Vec::new(),
        empty_witness: None,
        restored: None,
        interaction: None,
        diagram: None,
        path: None,
        transfer: None,
        robustness: None,
        chevalley: None,
        observations: None,
        lift: None,
        artin: None,
        diagnostics: None,
        atlas: None,
    }
}

pub(crate) fn lift_outcome(
    verdict: Verdict,
    coeff_domain: CoeffDomain,
    point_domain: PointDomain,
    applicability: Vec<ApplicabilityCheck>,
    provenance: Provenance,
    detail: LiftOutcomeDetail,
) -> ShigureOutcome {
    ShigureOutcome {
        verdict,
        coeff_domain,
        point_domain,
        applicability,
        provenance,
        residual_ideal: detail.residual_in_m.clone(),
        empty_witness: None,
        restored: None,
        interaction: None,
        diagram: None,
        path: None,
        transfer: None,
        robustness: None,
        chevalley: None,
        observations: None,
        lift: Some(detail),
        artin: None,
        diagnostics: None,
        atlas: None,
    }
}

pub(crate) fn compute_etale_descent(
    et: &FiniteEtaleDescentSpec,
    coeff_domain: &CoeffDomain,
) -> Result<FiniteEtaleDescentResult, SilenceReason> {
    let d = et.degree;
    let cover_equation = format!("{}^{d} - {} = 0", et.cover_var, et.base_var);

    // 1. 多項式 f(z, t) = z^d - t を構築し、partial_derivative で導関数 ∂f/∂z を実計算する。
    let z_var = Poly::var(2, 0, BigInt::zero());
    let t_var = Poly::var(2, 1, BigInt::zero());
    let z_pow_d = z_var.checked_pow(d).map_err(map_lift_algebra_error)?;
    let cover_poly = z_pow_d.sub(&t_var);
    let df_dz = cover_poly
        .partial_derivative(0)
        .map_err(map_lift_algebra_error)?;
    let deriv_coeff = df_dz
        .terms()
        .values()
        .next()
        .cloned()
        .unwrap_or_else(BigInt::zero);

    let derivative_unit_verified = match coeff_domain {
        CoeffDomain::Q => Rat::from_int(deriv_coeff.clone()).coeff_inv().is_some(),
        CoeffDomain::Fp(p) => FpElem::from_checked_prime(deriv_coeff.clone(), p.clone())
            .coeff_inv()
            .is_some(),
        CoeffDomain::Z => deriv_coeff == BigInt::one() || deriv_coeff == -BigInt::one(),
    };

    if !et.base_invertible || !derivative_unit_verified {
        let detail = if !et.base_invertible {
            format!(
                "base variable `{}` is not inverted; cover ramifies at {} = 0 (C9 not applicable)",
                et.base_var, et.base_var
            )
        } else {
            format!(
                "derivative {deriv_coeff}*{}^({}) is not a unit over {coeff_domain} (C9 not finite etale)",
                et.cover_var,
                d - 1
            )
        };
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "finite_etale_cover_applicable".to_owned(),
            detail,
        });
    }

    // 2. 被覆 E 上の対角局所断面 s_diag(z) = z が f(z, z^d) = 0 を満たすことを代入検算する。
    let diag_eval = cover_poly
        .substitute(&[z_var, z_pow_d])
        .map_err(map_lift_algebra_error)?;
    let local_selection_exists_on_cover = diag_eval.is_zero();

    // 3. ファイバー積 E ×_B E の μ_d-torsor 関係と三重交差 cocycle 恒等式を多項式計算で検証する。
    let cocycle_verified = verify_mu_d_cocycle_identities(d, coeff_domain)?;

    // 4. 基底 G_m = Spec k[t, t^-1] 上の大域正則断面 h(t)^d = t の単元指数方程式 d*m = 1 を
    //    整数線形計算核 solve_affine_z で厳密に解く。
    let global_regular_section_exists = matches!(
        solve_affine_z(&[vec![BigInt::from(d)]], &[BigInt::one()], 1)
            .map_err(map_lift_algebra_error)?,
        AffineSolutionZ::Consistent { .. }
    );

    let nonexistence_reason = if global_regular_section_exists {
        "global regular section exists".to_owned()
    } else {
        format!(
            "unit exponent obstruction: h({})^{d} = {} requires {d}*m = 1 in Z (inconsistent by SNF), so no global regular section exists in {coeff_domain}[{}, {}^-1]",
            et.base_var, et.base_var, et.base_var, et.base_var
        )
    };
    Ok(FiniteEtaleDescentResult {
        cover_equation,
        degree: d,
        is_finite_etale: true,
        derivative_unit_verified,
        cocycle_group: format!("mu_{d}"),
        cocycle_verified,
        local_selection_exists_on_cover,
        global_regular_section_exists,
        nonexistence_reason,
    })
}

fn verify_mu_d_cocycle_identities(
    d: u32,
    coeff_domain: &CoeffDomain,
) -> Result<bool, SilenceReason> {
    // 変数 (z1, w12, w23) 上で z2 = w12*z1, z3 = w23*z2, w13 = w12*w23 として
    // (a) z2^d - z1^d == z1^d * (w12^d - 1)
    // (b) z3 - w13*z1 == 0
    // (c) w13^d - 1 ∈ <w12^d - 1, w23^d - 1>（体上の ideal 所属検査）
    let z1 = Poly::var(3, 0, BigInt::zero());
    let w12 = Poly::var(3, 1, BigInt::zero());
    let w23 = Poly::var(3, 2, BigInt::zero());
    let one = Poly::one(3, BigInt::zero());
    let z2 = w12.checked_mul(&z1).map_err(map_lift_algebra_error)?;
    let z3 = w23.checked_mul(&z2).map_err(map_lift_algebra_error)?;
    let w13 = w12.checked_mul(&w23).map_err(map_lift_algebra_error)?;
    let z1_d = z1.checked_pow(d).map_err(map_lift_algebra_error)?;
    let z2_d = z2.checked_pow(d).map_err(map_lift_algebra_error)?;
    let w12_d_m1 = w12.checked_pow(d).map_err(map_lift_algebra_error)?.sub(&one);
    let pairwise_ok = z2_d.sub(&z1_d) == z1_d.checked_mul(&w12_d_m1).map_err(map_lift_algebra_error)?;
    let triple_ok = z3
        .sub(&w13.checked_mul(&z1).map_err(map_lift_algebra_error)?)
        .is_zero();

    let vars = VarOrder::new(vec!["w12".to_owned(), "w23".to_owned()])
        .map_err(map_lift_algebra_error)?;
    let ideal_ok = match coeff_domain {
        CoeffDomain::Q => {
            let a = Poly::var(2, 0, Rat::zero());
            let b = Poly::var(2, 1, Rat::zero());
            let o = Poly::one(2, Rat::zero());
            let g1 = a.checked_pow(d).map_err(map_lift_algebra_error)?.sub(&o);
            let g2 = b.checked_pow(d).map_err(map_lift_algebra_error)?.sub(&o);
            let tgt = a
                .checked_mul(&b)
                .map_err(map_lift_algebra_error)?
                .checked_pow(d)
                .map_err(map_lift_algebra_error)?
                .sub(&o);
            ideal_membership_field(
                &tgt,
                &[g1, g2],
                &vars,
                MonomialOrder::Grevlex,
                DEFAULT_MAX_SYZYGY_PAIRS,
            )
            .map_err(map_lift_algebra_error)?
            .is_some()
        }
        CoeffDomain::Fp(p) => {
            let zero = FpElem::from_checked_prime(BigInt::zero(), p.clone());
            let a = Poly::var(2, 0, zero.clone());
            let b = Poly::var(2, 1, zero.clone());
            let o = Poly::one(2, zero);
            let g1 = a.checked_pow(d).map_err(map_lift_algebra_error)?.sub(&o);
            let g2 = b.checked_pow(d).map_err(map_lift_algebra_error)?.sub(&o);
            let tgt = a
                .checked_mul(&b)
                .map_err(map_lift_algebra_error)?
                .checked_pow(d)
                .map_err(map_lift_algebra_error)?
                .sub(&o);
            ideal_membership_field(
                &tgt,
                &[g1, g2],
                &vars,
                MonomialOrder::Grevlex,
                DEFAULT_MAX_SYZYGY_PAIRS,
            )
            .map_err(map_lift_algebra_error)?
            .is_some()
        }
        CoeffDomain::Z => false,
    };
    Ok(pairwise_ok && triple_ok && ideal_ok)
}

// =========================================================================
// 共通補助ヘルパ（lift_z からも参照）
// =========================================================================

pub(crate) fn check_cover_support_closure(
    cov: &DeclarationCoverSpec,
    spec_vars: &[String],
    laws: &[NamedPoly],
) -> (bool, Vec<String>) {
    let law_map: BTreeMap<&str, &NamedPoly> =
        laws.iter().map(|l| (l.name.as_str(), l)).collect();
    let mut unclosed = Vec::new();
    let mut covered_vars: BTreeSet<&str> = BTreeSet::new();
    let mut covered_laws: BTreeSet<&str> = BTreeSet::new();
    for c in &cov.contexts {
        let allowed: BTreeSet<&str> = c.vars.iter().map(String::as_str).collect();
        covered_vars.extend(allowed.iter().copied());
        for law_name in &c.laws {
            covered_laws.insert(law_name.as_str());
            if let Some(law) = law_map.get(law_name.as_str()) {
                let mut used = BTreeSet::new();
                collect_state_vars(&law.expr, &mut used);
                let outside: Vec<&str> = used
                    .iter()
                    .copied()
                    .filter(|v| !allowed.contains(v))
                    .collect();
                if !outside.is_empty() {
                    unclosed.push(format!(
                        "{}.law:{}(references outside vars: {})",
                        c.name,
                        law.name,
                        outside.join(", ")
                    ));
                }
            }
        }
        for obs in &c.observations {
            let mut used = BTreeSet::new();
            collect_state_vars(&obs.expr, &mut used);
            let outside: Vec<&str> = used
                .iter()
                .copied()
                .filter(|v| !allowed.contains(v))
                .collect();
            if !outside.is_empty() {
                unclosed.push(format!(
                    "{}.{}(references outside vars: {})",
                    c.name,
                    obs.name,
                    outside.join(", ")
                ));
            }
        }
    }
    for v in spec_vars {
        if !covered_vars.contains(v.as_str()) {
            unclosed.push(format!("uncovered_var:{v}"));
        }
    }
    for l in laws {
        if !covered_laws.contains(l.name.as_str()) {
            unclosed.push(format!("uncovered_law:{}", l.name));
        }
    }
    (unclosed.is_empty(), unclosed)
}

fn collect_state_vars<'a>(expr: &'a PolyExpr, out: &mut BTreeSet<&'a str>) {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        match node {
            PolyExpr::StateVar(v) => {
                out.insert(v.as_str());
            }
            PolyExpr::Neg(a) | PolyExpr::Pow(a, _) => stack.push(a),
            PolyExpr::Add(a, b) | PolyExpr::Sub(a, b) | PolyExpr::Mul(a, b) => {
                stack.push(b);
                stack.push(a);
            }
            PolyExpr::Const(_)
            | PolyExpr::ArgVar(_)
            | PolyExpr::ParamVar(_)
            | PolyExpr::Unobserved { .. } => {}
        }
    }
}

pub(crate) fn apply_rp_subset_shift<C: RingCoeff>(
    base_rp: &[Vec<C>],
    allowed_indices: &[usize],
    dp: usize,
    subset_delta: &[C],
    ext: &SquareZeroExtension<C>,
) -> Vec<Vec<C>> {
    let mut out = base_rp.to_vec();
    for (pos, &v_idx) in allowed_indices.iter().enumerate() {
        let slice = &subset_delta[pos * dp..(pos + 1) * dp];
        out[v_idx] = ext.r_prime().add(&out[v_idx], slice);
    }
    out
}

pub(crate) fn format_subset_rp_map<C: RingCoeff>(
    allowed_vars: &[String],
    vec: &[C],
    dp: usize,
    ext: &SquareZeroExtension<C>,
) -> BTreeMap<String, String> {
    allowed_vars
        .iter()
        .enumerate()
        .map(|(i, name)| (name.clone(), ext.r_prime().format_elem(&vec[i * dp..(i + 1) * dp])))
        .collect()
}

pub(crate) fn expand_subset_delta<C: Clone>(
    total_vars: usize,
    allowed_indices: &[usize],
    dm: usize,
    subset_vec: &[C],
    zero: &C,
) -> Vec<C> {
    let mut out = vec![zero.clone(); total_vars * dm];
    for (pos, &v_idx) in allowed_indices.iter().enumerate() {
        for k in 0..dm {
            out[v_idx * dm + k] = subset_vec[pos * dm + k].clone();
        }
    }
    out
}

pub(crate) fn format_subset_m_map<C: RingCoeff>(
    allowed_vars: &[String],
    vec_m: &[C],
    ext: &SquareZeroExtension<C>,
) -> BTreeMap<String, String> {
    let dm = ext.kernel_dim();
    allowed_vars
        .iter()
        .enumerate()
        .map(|(i, name)| {
            let slice = &vec_m[i * dm..(i + 1) * dm];
            let s = match ext.embed_kernel(slice) {
                Ok(e) => ext.r_prime().format_elem(&e),
                Err(_) => "0".to_owned(),
            };
            (name.clone(), s)
        })
        .collect()
}
