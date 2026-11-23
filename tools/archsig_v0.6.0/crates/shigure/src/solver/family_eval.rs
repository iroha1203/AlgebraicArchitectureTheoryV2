//! 複数解釈族・共有規則族の有限点列挙と 1 変数有理根定理。

use crate::algebra::{
    AffineSolutionQ, AffineSolutionZ, ExprBindings, FpElem, GroebnerBasis, MonomialOrder, Poly,
    Rat, VarOrder, rabinowitsch_solve, solve_affine_q, solve_affine_z, solve_fp_enumeration,
};
use crate::ir::change::{NamedPoly, PointDomain};
use crate::ir::family::{CandidateSpace, CheckedFamilySpec, RealizationSpace};
use crate::ir::presentation::{CoordValue, Presentation};
use crate::ir::provenance::SourceRef;
use crate::ir::result::{EmptyWitness, SilenceReason};
use crate::ir::result_phase3::RealizationWitness;
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::solver::context::{clear_denominators_to_z, display_polys};
use crate::solver::preservation::map_algebra_silence;
use crate::solver::restore::polys_to_affine_system_q;
use archsig_common::prime::is_prime;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};
use std::collections::{BTreeMap, BTreeSet};

/// 有限列挙型実現族・候補族・Fp 点全列挙の上限。
pub const DEFAULT_MAX_ENUM_POINTS: usize = 256;

const MAX_RATIONAL_ROOT_COEFF: u64 = 1_000_000_000;
const MAX_RATIONAL_ROOT_DIVISORS: usize = 4_096;

/// 係数域に応じた正確なスカラー値。
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ScalarVal {
    Q(Rat),
    Z(BigInt),
    Fp(FpElem),
}

impl ScalarVal {
    pub(crate) fn from_lit(lit: &ScalarLit, domain: &CoeffDomain) -> Result<Self, SilenceReason> {
        match (lit, domain) {
            (ScalarLit::Q { num, den }, CoeffDomain::Q) => Rat::new(num.clone(), den.clone())
                .map(ScalarVal::Q)
                .ok_or_else(|| SilenceReason::ApplicabilityConditionNotMet {
                    condition: "valid_rational_literal".to_owned(),
                    detail: "zero denominator in rational literal".to_owned(),
                }),
            (ScalarLit::Z(z), CoeffDomain::Q) => Ok(ScalarVal::Q(Rat::from_int(z.clone()))),
            (ScalarLit::Z(z), CoeffDomain::Z) => Ok(ScalarVal::Z(z.clone())),
            (ScalarLit::Fp { value, modulus }, CoeffDomain::Fp(p)) if modulus == p => {
                if !is_prime(p) {
                    return Err(SilenceReason::ApplicabilityConditionNotMet {
                        condition: "prime_modulus".to_owned(),
                        detail: format!("modulus `{p}` is not prime"),
                    });
                }
                Ok(ScalarVal::Fp(FpElem::from_checked_prime(
                    BigInt::from(value.clone()),
                    p.clone(),
                )))
            }
            _ => Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "coeff_domain_match".to_owned(),
                detail: format!("literal {lit} does not match coefficient domain {domain}"),
            }),
        }
    }

    pub(crate) fn to_lit(&self) -> ScalarLit {
        match self {
            ScalarVal::Q(r) => r.to_scalar_lit(),
            ScalarVal::Z(z) => ScalarLit::Z(z.clone()),
            ScalarVal::Fp(f) => ScalarLit::Fp {
                value: f.value().clone(),
                modulus: f.modulus().clone(),
            },
        }
    }

    pub(crate) fn to_expr(&self) -> PolyExpr {
        PolyExpr::Const(self.to_lit())
    }

    pub(crate) fn to_display(&self) -> String {
        match self {
            ScalarVal::Q(r) => r.to_string(),
            ScalarVal::Z(z) => z.to_string(),
            ScalarVal::Fp(f) => f.to_string(),
        }
    }

    pub(crate) fn is_zero(&self) -> bool {
        match self {
            ScalarVal::Q(r) => r.is_zero(),
            ScalarVal::Z(z) => z.is_zero(),
            ScalarVal::Fp(f) => f.is_zero(),
        }
    }

    pub(crate) fn is_unit(&self) -> bool {
        match self {
            ScalarVal::Q(r) => !r.is_zero(),
            ScalarVal::Z(z) => z.abs().is_one(),
            ScalarVal::Fp(f) => !f.is_zero(),
        }
    }

    pub(crate) fn as_rat(&self) -> Rat {
        match self {
            ScalarVal::Q(r) => r.clone(),
            ScalarVal::Z(z) => Rat::from_int(z.clone()),
            ScalarVal::Fp(_) => panic!("cannot lift Fp element to Q"),
        }
    }
}

/// 有限点または有限メンバーとして具象化された実現 $u \in U_b$。
#[derive(Clone, Debug)]
pub(crate) struct EnumRealization {
    pub member_id: Option<String>,
    pub values: Vec<ScalarVal>,
    pub assignments: BTreeMap<String, String>,
    pub is_raw_candidate: bool,
    pub origin: SourceRef,
    pub presentation: Option<Presentation>,
}

impl EnumRealization {
    pub(crate) fn to_witness(&self) -> RealizationWitness {
        RealizationWitness {
            member_id: self.member_id.clone(),
            assignments: self.assignments.clone(),
            is_raw_candidate: self.is_raw_candidate,
            origin: self.origin.clone(),
        }
    }
}

/// 有限点または有限メンバーとして具象化された共有候補 $c \in C_b$。
#[derive(Clone, Debug)]
pub(crate) struct EnumCandidate {
    pub candidate_id: Option<String>,
    pub values: Vec<ScalarVal>,
    pub assignments: BTreeMap<String, String>,
    pub origin: SourceRef,
}

#[derive(Clone, Debug)]
pub(crate) enum RealizationFiberEnum {
    Finite(Vec<EnumRealization>),
    NonFiniteScheme {
        sample_witness: Option<RealizationWitness>,
    },
}

#[derive(Clone, Debug)]
pub(crate) enum CandidateFiberEnum {
    Finite(Vec<EnumCandidate>),
    NonFiniteScheme,
}

pub(crate) fn build_assignment_map(
    names: &[String],
    vals: &[ScalarVal],
) -> BTreeMap<String, String> {
    names
        .iter()
        .zip(vals)
        .map(|(n, v)| (n.clone(), v.to_display()))
        .collect()
}

pub(crate) fn eval_expr_at(
    expr: &PolyExpr,
    vars: &VarOrder,
    vals: &[ScalarVal],
    domain: &CoeffDomain,
) -> Result<ScalarVal, SilenceReason> {
    let bind = ExprBindings::params_only(vars);
    match domain {
        CoeffDomain::Q => {
            let p = Poly::from_expr_q(expr, &bind).map_err(map_algebra_silence)?;
            let rs: Vec<Rat> = vals.iter().map(ScalarVal::as_rat).collect();
            Ok(ScalarVal::Q(p.eval_at(&rs).map_err(map_algebra_silence)?))
        }
        CoeffDomain::Z => {
            let p = Poly::from_expr_z(expr, &bind).map_err(map_algebra_silence)?;
            let zs: Vec<BigInt> = vals
                .iter()
                .map(|v| match v {
                    ScalarVal::Z(z) => z.clone(),
                    _ => unreachable!("Z domain expected"),
                })
                .collect();
            Ok(ScalarVal::Z(p.eval_at(&zs).map_err(map_algebra_silence)?))
        }
        CoeffDomain::Fp(m) => {
            let p = Poly::from_expr_fp(expr, &bind, m).map_err(map_algebra_silence)?;
            let fs: Vec<FpElem> = vals
                .iter()
                .map(|v| match v {
                    ScalarVal::Fp(f) => f.clone(),
                    _ => unreachable!("Fp domain expected"),
                })
                .collect();
            Ok(ScalarVal::Fp(p.eval_at(&fs).map_err(map_algebra_silence)?))
        }
    }
}

/// 1 変数多項式 $p(x) \in \mathbb{Q}[x]$ に対する汎用有理根定理。
/// 返り値第 2 要素 `exhausts_closure` は、返された有理根の重複度和が次数と一致し
/// 代数閉包上に他の根がないとき `true`。
pub(crate) fn univariate_rational_roots(
    poly: &Poly<Rat>,
) -> Result<(Vec<Rat>, bool), SilenceReason> {
    if poly.num_vars() != 1 {
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "univariate_polynomial_required".to_owned(),
            detail: format!("expected 1 variable, got {}", poly.num_vars()),
        });
    }
    if poly.is_zero() {
        return Err(SilenceReason::FiniteEnumerationOutOfScope {
            detail: "zero polynomial has infinitely many rational roots".to_owned(),
        });
    }
    let deg = poly.total_degree() as usize;
    if deg == 0 {
        return Ok((vec![], true));
    }

    let mut lcm_den = BigInt::one();
    for c in poly.terms().values() {
        lcm_den = lcm_den.lcm(c.den());
    }
    let mut coeffs = vec![BigInt::zero(); deg + 1];
    for (m, c) in poly.terms() {
        coeffs[m.exps()[0] as usize] = c.num() * (&lcm_den / c.den());
    }
    let limit = BigInt::from(MAX_RATIONAL_ROOT_COEFF);
    if coeffs.iter().any(|c| c.abs() > limit) {
        return Err(SilenceReason::NonLinearRationalOrIntegerExistence {
            point_domain: PointDomain::RationalPoints,
            detail: format!(
                "univariate polynomial coefficient magnitude exceeds {MAX_RATIONAL_ROOT_COEFF}"
            ),
        });
    }

    let mut roots = Vec::new();
    let mut first_nz = 0usize;
    while first_nz <= deg && coeffs[first_nz].is_zero() {
        first_nz += 1;
    }
    if first_nz > 0 {
        roots.push(Rat::zero());
    }
    let trimmed = &coeffs[first_nz..];
    if trimmed.len() <= 1 {
        return Ok((roots, true));
    }

    let a0 = trimmed[0].abs().to_u64().unwrap_or(u64::MAX);
    let ad = trimmed[trimmed.len() - 1]
        .abs()
        .to_u64()
        .unwrap_or(u64::MAX);
    let num_divs = positive_divisors_u64(a0)?;
    let den_divs = positive_divisors_u64(ad)?;
    let mut candidates = BTreeSet::new();
    for p in &num_divs {
        for q in &den_divs {
            if let Some(pos) = Rat::new(BigInt::from(*p), BigInt::from(*q)) {
                candidates.insert(pos.clone());
                candidates.insert(-pos);
            }
        }
    }

    let mut poly_coeffs: Vec<Rat> = coeffs.iter().map(|z| Rat::from_int(z.clone())).collect();
    for cand in candidates {
        if eval_univariate_horner(&poly_coeffs, &cand).is_zero() {
            roots.push(cand.clone());
            while eval_univariate_horner(&poly_coeffs, &cand).is_zero() {
                poly_coeffs = synthetic_div_linear(&poly_coeffs, &cand);
            }
        }
    }
    let exhausted = poly_coeffs.len() == 1;
    roots.sort();
    roots.dedup();
    Ok((roots, exhausted))
}

fn positive_divisors_u64(n: u64) -> Result<Vec<u64>, SilenceReason> {
    if n == 0 {
        return Ok(vec![1]);
    }
    let mut divs = Vec::new();
    let mut d = 1u64;
    while d * d <= n {
        if n.is_multiple_of(d) {
            divs.push(d);
            if d != n / d {
                divs.push(n / d);
            }
            if divs.len() > MAX_RATIONAL_ROOT_DIVISORS {
                return Err(SilenceReason::NonLinearRationalOrIntegerExistence {
                    point_domain: PointDomain::RationalPoints,
                    detail: format!("divisor count exceeded {MAX_RATIONAL_ROOT_DIVISORS}"),
                });
            }
        }
        d += 1;
    }
    divs.sort_unstable();
    Ok(divs)
}

fn eval_univariate_horner(coeffs: &[Rat], x: &Rat) -> Rat {
    let mut acc = Rat::zero();
    for c in coeffs.iter().rev() {
        acc = &(&acc * x) + c;
    }
    acc
}

fn synthetic_div_linear(coeffs: &[Rat], root: &Rat) -> Vec<Rat> {
    if coeffs.len() <= 1 {
        return coeffs.to_vec();
    }
    let deg = coeffs.len() - 1;
    let mut quot = vec![Rat::zero(); deg];
    let mut acc = coeffs[deg].clone();
    quot[deg - 1] = acc.clone();
    for i in (1..deg).rev() {
        acc = &(&acc * root) + &coeffs[i];
        quot[i - 1] = acc.clone();
    }
    quot
}

pub(crate) fn map_scalar_assignments(
    var_names: &[String],
    assignments: &BTreeMap<String, CoordValue>,
    domain: &CoeffDomain,
) -> Result<(Vec<ScalarVal>, BTreeMap<String, String>), SilenceReason> {
    let mut vals = Vec::with_capacity(var_names.len());
    let mut disp = BTreeMap::new();
    for v in var_names {
        let Some(cv) = assignments.get(v) else {
            return Err(SilenceReason::UnobservedDependency {
                slots: vec![v.clone()],
            });
        };
        let lit = match cv {
            CoordValue::Observed(lit) => lit,
            CoordValue::Missing => {
                return Err(SilenceReason::UnobservedDependency {
                    slots: vec![v.clone()],
                });
            }
            CoordValue::Symbolic => {
                return Err(SilenceReason::ApplicabilityConditionNotMet {
                    condition: "finite_member_observed".to_owned(),
                    detail: format!("coordinate `{v}` is symbolic in finite member"),
                });
            }
        };
        let sv = ScalarVal::from_lit(lit, domain)?;
        disp.insert(v.clone(), sv.to_display());
        vals.push(sv);
    }
    Ok((vals, disp))
}

pub(crate) fn enumerate_realizations_for_base(
    family: &CheckedFamilySpec,
    base_value: &[ScalarLit],
    point_domain: &PointDomain,
    max_points: usize,
) -> Result<(RealizationFiberEnum, Option<EmptyWitness>), SilenceReason> {
    let inner = family.inner();
    let domain = family.coeff_domain();
    let u_names = family.u_vars();
    let u_vars = VarOrder::new(u_names.to_vec()).map_err(map_algebra_silence)?;
    let target_b: Vec<ScalarVal> = base_value
        .iter()
        .map(|l| ScalarVal::from_lit(l, domain))
        .collect::<Result<Vec<_>, _>>()?;

    match &inner.realizations.space {
        RealizationSpace::FiniteMembers(members) => {
            if members.len() > max_points {
                return Err(SilenceReason::FiniteEnumerationOutOfScope {
                    detail: format!(
                        "realization member count {} exceeds enumeration limit ({max_points})",
                        members.len()
                    ),
                });
            }
            let mut out = Vec::new();
            for m in members {
                let (vals, disp) = map_scalar_assignments(u_names, &m.assignments, domain)?;
                let mut matches = true;
                for (q_expr, b_val) in inner.realizations.reading_q.iter().zip(&target_b) {
                    if &eval_expr_at(q_expr, &u_vars, &vals, domain)? != b_val {
                        matches = false;
                        break;
                    }
                }
                if matches {
                    out.push(EnumRealization {
                        member_id: Some(m.id.clone()),
                        values: vals,
                        assignments: disp,
                        is_raw_candidate: m.is_raw_candidate,
                        origin: m.origin.clone(),
                        presentation: m.presentation.clone(),
                    });
                }
            }
            Ok((RealizationFiberEnum::Finite(out), None))
        }
        RealizationSpace::PolynomialScheme {
            equations,
            invertibles,
            is_raw_candidate,
            origin,
        } => enumerate_scheme_realizations(
            u_names,
            &u_vars,
            equations,
            invertibles,
            &inner.realizations.reading_q,
            base_value,
            domain,
            point_domain,
            *is_raw_candidate,
            origin,
            max_points,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn enumerate_scheme_realizations(
    u_names: &[String],
    u_vars: &VarOrder,
    equations: &[NamedPoly],
    invertibles: &[NamedPoly],
    reading_q: &[PolyExpr],
    base_value: &[ScalarLit],
    domain: &CoeffDomain,
    point_domain: &PointDomain,
    is_raw_candidate: bool,
    origin: &SourceRef,
    max_points: usize,
) -> Result<(RealizationFiberEnum, Option<EmptyWitness>), SilenceReason> {
    let bind = ExprBindings::params_only(u_vars);
    let mut eq_exprs: Vec<PolyExpr> = equations.iter().map(|e| e.expr.clone()).collect();
    for (q_expr, b_lit) in reading_q.iter().zip(base_value) {
        eq_exprs.push(PolyExpr::diff(
            q_expr.clone(),
            PolyExpr::Const(b_lit.clone()),
        ));
    }
    let inv_exprs: Vec<PolyExpr> = invertibles.iter().map(|i| i.expr.clone()).collect();

    if let CoeffDomain::Fp(p) = domain {
        let eqs: Vec<Poly<FpElem>> = eq_exprs
            .iter()
            .map(|e| Poly::from_expr_fp(e, &bind, p))
            .collect::<Result<_, _>>()
            .map_err(map_algebra_silence)?;
        let invs: Vec<Poly<FpElem>> = inv_exprs
            .iter()
            .map(|e| Poly::from_expr_fp(e, &bind, p))
            .collect::<Result<_, _>>()
            .map_err(map_algebra_silence)?;
        let sol =
            solve_fp_enumeration(&eqs, &invs, u_names.len(), p, max_points).map_err(|_| {
                SilenceReason::FiniteEnumerationOutOfScope {
                    detail: format!(
                        "Fp({p}) realization enumeration exceeded limit ({max_points})"
                    ),
                }
            })?;
        if sol.solutions.len() > max_points {
            return Err(SilenceReason::FiniteEnumerationOutOfScope {
                detail: format!(
                    "Fp({p}) realization count {} exceeds limit ({max_points})",
                    sol.solutions.len()
                ),
            });
        }
        let members = sol
            .solutions
            .into_iter()
            .map(|pt| {
                let vals: Vec<ScalarVal> = pt.into_iter().map(ScalarVal::Fp).collect();
                let assignments = build_assignment_map(u_names, &vals);
                EnumRealization {
                    member_id: None,
                    values: vals,
                    assignments,
                    is_raw_candidate,
                    origin: origin.clone(),
                    presentation: None,
                }
            })
            .collect();
        return Ok((RealizationFiberEnum::Finite(members), None));
    }

    let eqs_q: Vec<Poly<Rat>> = eq_exprs
        .iter()
        .map(|e| Poly::from_expr_q(e, &bind))
        .collect::<Result<_, _>>()
        .map_err(map_algebra_silence)?;
    let invs_q: Vec<Poly<Rat>> = inv_exprs
        .iter()
        .map(|e| Poly::from_expr_q(e, &bind))
        .collect::<Result<_, _>>()
        .map_err(map_algebra_silence)?;

    let rab = rabinowitsch_solve(&eqs_q, &invs_q, u_vars).map_err(map_algebra_silence)?;
    if rab.is_empty_over_closure {
        return Ok((RealizationFiberEnum::Finite(vec![]), rab.empty_witness));
    }

    if u_names.is_empty() {
        let assignments = BTreeMap::new();
        return Ok((
            RealizationFiberEnum::Finite(vec![EnumRealization {
                member_id: None,
                values: vec![],
                assignments,
                is_raw_candidate,
                origin: origin.clone(),
                presentation: None,
            }]),
            None,
        ));
    }

    if rab.parameter_equations.iter().all(Poly::is_affine) {
        let (mat, rhs) = polys_to_affine_system_q(&rab.parameter_equations, u_names.len())?;
        if let AffineSolutionQ::Consistent {
            particular,
            kernel_basis,
            verified: true,
        } = solve_affine_q(&mat, &rhs, u_names.len()).map_err(map_algebra_silence)?
            && kernel_basis.is_empty()
        {
            let inv_ok = invs_q.iter().all(|iv| {
                iv.eval_at(&particular).is_ok_and(|v| match point_domain {
                    PointDomain::IntegerPoints => v.den().is_one() && v.num().abs().is_one(),
                    _ => !v.is_zero(),
                })
            });
            let domain_ok = match point_domain {
                PointDomain::IntegerPoints => particular.iter().all(|v| v.den().is_one()),
                _ => true,
            };
            if !inv_ok || !domain_ok {
                return Ok((RealizationFiberEnum::Finite(vec![]), None));
            }
            let vals: Vec<ScalarVal> = particular
                .iter()
                .map(|r| match domain {
                    CoeffDomain::Z => ScalarVal::Z(r.num().clone()),
                    _ => ScalarVal::Q(r.clone()),
                })
                .collect();
            let assignments = build_assignment_map(u_names, &vals);
            return Ok((
                RealizationFiberEnum::Finite(vec![EnumRealization {
                    member_id: None,
                    values: vals,
                    assignments,
                    is_raw_candidate,
                    origin: origin.clone(),
                    presentation: None,
                }]),
                None,
            ));
        }
    }

    if u_names.len() == 1 && !rab.parameter_equations.is_empty() {
        let gb = GroebnerBasis::compute(
            &rab.parameter_equations,
            u_vars.clone(),
            MonomialOrder::Grevlex,
        )
        .map_err(map_algebra_silence)?;
        let gens = gb.basis_polys();
        if gens.len() == 1 && !gens[0].is_zero() {
            let (roots, exhausted) = univariate_rational_roots(gens[0])?;
            let valid_roots: Vec<Rat> = roots
                .into_iter()
                .filter(|r| {
                    let pt = vec![r.clone()];
                    let int_ok = *point_domain != PointDomain::IntegerPoints || r.den().is_one();
                    let inv_ok = invs_q.iter().all(|iv| {
                        iv.eval_at(&pt).is_ok_and(|v| match point_domain {
                            PointDomain::IntegerPoints => {
                                v.den().is_one() && v.num().abs().is_one()
                            }
                            _ => !v.is_zero(),
                        })
                    });
                    int_ok && inv_ok
                })
                .collect();
            if *point_domain != PointDomain::AlgebraicClosure || exhausted {
                let members = valid_roots
                    .into_iter()
                    .map(|r| {
                        let sv = match domain {
                            CoeffDomain::Z => ScalarVal::Z(r.num().clone()),
                            _ => ScalarVal::Q(r),
                        };
                        let vals = vec![sv];
                        let assignments = build_assignment_map(u_names, &vals);
                        EnumRealization {
                            member_id: None,
                            values: vals,
                            assignments,
                            is_raw_candidate,
                            origin: origin.clone(),
                            presentation: None,
                        }
                    })
                    .collect();
                return Ok((RealizationFiberEnum::Finite(members), None));
            }
        }
    }

    if matches!(
        point_domain,
        PointDomain::RationalPoints | PointDomain::IntegerPoints
    ) {
        if *point_domain == PointDomain::IntegerPoints
            && rab.parameter_equations.iter().all(Poly::is_affine)
            && !rab.parameter_equations.is_empty()
            && invs_q.is_empty()
        {
            let eqs_z = clear_denominators_to_z(&rab.parameter_equations);
            if let Ok((mat, rhs)) =
                crate::solver::restore::polys_to_affine_system_z(&eqs_z, u_names.len())
            {
                match solve_affine_z(&mat, &rhs, u_names.len()) {
                    Ok(AffineSolutionZ::Consistent {
                        particular,
                        kernel_basis,
                        verified: true,
                        ..
                    }) if kernel_basis.is_empty() => {
                        let vals: Vec<ScalarVal> =
                            particular.into_iter().map(ScalarVal::Z).collect();
                        let assignments = build_assignment_map(u_names, &vals);
                        return Ok((
                            RealizationFiberEnum::Finite(vec![EnumRealization {
                                member_id: None,
                                values: vals,
                                assignments,
                                is_raw_candidate,
                                origin: origin.clone(),
                                presentation: None,
                            }]),
                            None,
                        ));
                    }
                    Ok(AffineSolutionZ::Inconsistent { verified: true, .. }) => {
                        return Ok((RealizationFiberEnum::Finite(vec![]), None));
                    }
                    _ => {}
                }
            }
        }
        return Err(SilenceReason::NonLinearRationalOrIntegerExistence {
            point_domain: point_domain.clone(),
            detail:
                "cannot finitely enumerate nonlinear or infinite rational/integer realization fiber"
                    .to_owned(),
        });
    }

    let sample_witness = Some(build_symbolic_realization_witness(
        u_names,
        u_vars,
        &rab.parameter_equations,
        is_raw_candidate,
        origin,
    ));
    Ok((
        RealizationFiberEnum::NonFiniteScheme { sample_witness },
        None,
    ))
}

fn build_symbolic_realization_witness(
    u_names: &[String],
    u_vars: &VarOrder,
    param_eqs: &[Poly<Rat>],
    is_raw_candidate: bool,
    origin: &SourceRef,
) -> RealizationWitness {
    let mut assignments = BTreeMap::new();
    if param_eqs.iter().all(Poly::is_affine)
        && let Ok((mat, rhs)) = polys_to_affine_system_q(param_eqs, u_names.len())
        && let Ok(AffineSolutionQ::Consistent { particular, .. }) =
            solve_affine_q(&mat, &rhs, u_names.len())
    {
        for (n, v) in u_names.iter().zip(&particular) {
            assignments.insert(n.clone(), v.to_string());
        }
        return RealizationWitness {
            member_id: None,
            assignments,
            is_raw_candidate,
            origin: origin.clone(),
        };
    }
    let eqs_str = display_polys(param_eqs, u_vars);
    for n in u_names {
        let desc = if eqs_str.is_empty() {
            n.clone()
        } else {
            format!("generic({n}; {} = 0)", eqs_str.join(", "))
        };
        assignments.insert(n.clone(), desc);
    }
    RealizationWitness {
        member_id: None,
        assignments,
        is_raw_candidate,
        origin: origin.clone(),
    }
}

pub(crate) fn enumerate_candidates_for_base(
    family: &CheckedFamilySpec,
    base_value: &[ScalarLit],
    point_domain: &PointDomain,
    max_points: usize,
) -> Result<CandidateFiberEnum, SilenceReason> {
    let inner = family.inner();
    let domain = family.coeff_domain();
    let c_names = family.c_vars();
    let c_vars = VarOrder::new(c_names.to_vec()).map_err(map_algebra_silence)?;
    let target_b: Vec<ScalarVal> = base_value
        .iter()
        .map(|l| ScalarVal::from_lit(l, domain))
        .collect::<Result<Vec<_>, _>>()?;

    match &inner.candidates.space {
        CandidateSpace::FiniteMembers(members) => {
            if members.len() > max_points {
                return Err(SilenceReason::FiniteEnumerationOutOfScope {
                    detail: format!(
                        "candidate member count {} exceeds enumeration limit ({max_points})",
                        members.len()
                    ),
                });
            }
            let mut out = Vec::new();
            for m in members {
                let (vals, disp) = map_scalar_assignments(c_names, &m.assignments, domain)?;
                let mut matches = true;
                for (pi_expr, b_val) in inner.candidates.pi.iter().zip(&target_b) {
                    if &eval_expr_at(pi_expr, &c_vars, &vals, domain)? != b_val {
                        matches = false;
                        break;
                    }
                }
                if matches {
                    out.push(EnumCandidate {
                        candidate_id: Some(m.id.clone()),
                        values: vals,
                        assignments: disp,
                        origin: m.origin.clone(),
                    });
                }
            }
            Ok(CandidateFiberEnum::Finite(out))
        }
        CandidateSpace::PolynomialScheme {
            equations,
            invertibles,
            origin,
        } => {
            if let (RealizationFiberEnum::Finite(pts), _) = enumerate_scheme_realizations(
                c_names,
                &c_vars,
                equations,
                invertibles,
                &inner.candidates.pi,
                base_value,
                domain,
                point_domain,
                false,
                origin,
                max_points,
            )? {
                let out = pts
                    .into_iter()
                    .map(|p| EnumCandidate {
                        candidate_id: None,
                        values: p.values,
                        assignments: p.assignments,
                        origin: origin.clone(),
                    })
                    .collect();
                Ok(CandidateFiberEnum::Finite(out))
            } else {
                Ok(CandidateFiberEnum::NonFiniteScheme)
            }
        }
    }
}
