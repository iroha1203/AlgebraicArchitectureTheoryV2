//! Phase 2（図式補完・一段変更経路・合法状態移送）で共有する多項式系解法と Z 商環単位ピボット判定。

use crate::algebra::{
    AffineSolutionZ, AlgebraError, ExprBindings, FpElem, GroebnerBasis, Monomial, MonomialOrder,
    Poly, Rat, RingCoeff, VarOrder, rabinowitsch_solve, solve_affine_z, solve_fp_enumeration,
};
use crate::ir::change::{EvalCondition, PointDomain};
use crate::ir::provenance::MathClause;
use crate::ir::result::{ApplicabilityCheck, EmptyWitness, SilenceReason, Verdict};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::solver::common_solve_q::solve_q_system;
use crate::solver::context::display_polys;
use crate::solver::preservation::{
    PreservationObligation, extract_ambient_param_coeffs, map_algebra_silence,
};
use crate::solver::restore::{
    ExtractedSubstitutionQ, find_witness_point_z, polys_to_affine_system_z,
};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use std::collections::BTreeMap;

/// 多項式系を解いて得られた具体点・アフィン代入 witness。
#[derive(Clone, Debug)]
pub(crate) enum ParamWitness {
    QSubst {
        subst: ExtractedSubstitutionQ,
    },
    QPoint {
        point: Vec<Rat>,
        assignments: BTreeMap<String, String>,
    },
    ZPoint {
        point: Vec<BigInt>,
        assignments: BTreeMap<String, String>,
    },
    FpPoint {
        point: Vec<FpElem>,
        modulus: BigUint,
        assignments: BTreeMap<String, String>,
    },
}

impl ParamWitness {
    pub fn to_param_subst(&self, param_vars: &VarOrder) -> BTreeMap<String, PolyExpr> {
        match self {
            ParamWitness::QSubst { subst } => subst.param_subst.clone(),
            ParamWitness::QPoint { point, .. } => param_vars
                .vars()
                .iter()
                .zip(point)
                .map(|(n, r)| (n.clone(), rat_expr(r)))
                .collect(),
            ParamWitness::ZPoint { point, .. } => param_vars
                .vars()
                .iter()
                .zip(point)
                .map(|(n, z)| (n.clone(), PolyExpr::Const(ScalarLit::Z(z.clone()))))
                .collect(),
            ParamWitness::FpPoint { point, .. } => param_vars
                .vars()
                .iter()
                .zip(point)
                .map(|(n, f)| {
                    (
                        n.clone(),
                        PolyExpr::Const(ScalarLit::Fp {
                            value: f.value().clone(),
                            modulus: f.modulus().clone(),
                        }),
                    )
                })
                .collect(),
        }
    }

    pub fn display_assignments(&self) -> BTreeMap<String, String> {
        match self {
            ParamWitness::QSubst { subst } => subst.display_assignments.clone(),
            ParamWitness::QPoint { assignments, .. }
            | ParamWitness::ZPoint { assignments, .. }
            | ParamWitness::FpPoint { assignments, .. } => assignments.clone(),
        }
    }

    pub fn unassigned_parameters(&self) -> Vec<String> {
        match self {
            ParamWitness::QSubst { subst } => subst.unassigned_parameters.clone(),
            _ => vec![],
        }
    }

    pub fn free_parameters(&self) -> Vec<String> {
        match self {
            ParamWitness::QSubst { subst } => subst.free_parameters.clone(),
            _ => vec![],
        }
    }

    pub fn remaining_nonlinear(&self) -> &[Poly<Rat>] {
        match self {
            ParamWitness::QSubst { subst } => &subst.remaining_nonlinear,
            _ => &[],
        }
    }
}

pub(crate) fn rat_expr(r: &Rat) -> PolyExpr {
    if r.den().is_one() {
        PolyExpr::Const(ScalarLit::Z(r.num().clone()))
    } else {
        PolyExpr::Const(ScalarLit::Q {
            num: r.num().clone(),
            den: r.den().clone(),
        })
    }
}

/// Phase 2 共通ソルバの出力。
pub(crate) struct SystemSolveOutcome {
    pub verdict: Verdict,
    pub checks: Vec<ApplicabilityCheck>,
    pub residual_display: Vec<String>,
    pub empty_witness: Option<EmptyWitness>,
    pub witness: Option<ParamWitness>,
}

/// 複数の `EvalCondition` 間の `point_domain` 一致を検査し、既定の `PointDomain` を決める。
pub(crate) fn resolve_consistent_point_domain(
    coeff_domain: &CoeffDomain,
    eval_conds: &[&EvalCondition],
) -> Result<PointDomain, SilenceReason> {
    if let Some(first) = eval_conds.first() {
        for other in &eval_conds[1..] {
            if other.point_domain != first.point_domain {
                return Err(SilenceReason::ApplicabilityConditionNotMet {
                    condition: "consistent_point_domain".to_owned(),
                    detail: format!(
                        "conflicting point domains `{}` and `{}`",
                        first.point_domain, other.point_domain
                    ),
                });
            }
        }
        return Ok(first.point_domain.clone());
    }
    Ok(match coeff_domain {
        CoeffDomain::Q | CoeffDomain::Z => PointDomain::AlgebraicClosure,
        CoeffDomain::Fp(p) => PointDomain::FiniteFieldPoints(p.clone()),
    })
}

pub(crate) fn undetermined_system(
    checks: Vec<ApplicabilityCheck>,
    residual_display: Vec<String>,
    reason: SilenceReason,
) -> SystemSolveOutcome {
    SystemSolveOutcome {
        verdict: Verdict::Undetermined(reason),
        checks,
        residual_display,
        empty_witness: None,
        witness: None,
    }
}

pub(crate) fn refuted_system(
    checks: Vec<ApplicabilityCheck>,
    residual_display: Vec<String>,
    empty_witness: Option<EmptyWitness>,
) -> SystemSolveOutcome {
    SystemSolveOutcome {
        verdict: Verdict::Refuted,
        checks,
        residual_display,
        empty_witness,
        witness: None,
    }
}

pub(crate) type PolyPair<C> = (Vec<Poly<C>>, Vec<Poly<C>>);

pub(crate) fn collect_eval_and_extra<C: RingCoeff, F>(
    extra: &[PolyExpr],
    eval_conds: &[&EvalCondition],
    param_bind: &ExprBindings,
    convert: F,
) -> Result<PolyPair<C>, SilenceReason>
where
    F: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, crate::algebra::AlgebraError>,
{
    let mut eqs = Vec::new();
    let mut invs = Vec::new();
    for ex in extra {
        let p = convert(ex, param_bind).map_err(map_algebra_silence)?;
        if !p.is_zero() {
            eqs.push(p);
        }
    }
    for cond in eval_conds {
        for eq in &cond.equations {
            let p = convert(&eq.expr, param_bind).map_err(map_algebra_silence)?;
            if !p.is_zero() {
                eqs.push(p);
            }
        }
        for inv in &cond.invertibles {
            invs.push(convert(&inv.expr, param_bind).map_err(map_algebra_silence)?);
        }
    }
    Ok((eqs, invs))
}

/// 任意の数の保存義務・追加パラメータ等式・複数の評価条件を統一的に解く。
pub(crate) fn solve_obligations_and_evals(
    obligations: &[PreservationObligation],
    extra_param_eqs: &[PolyExpr],
    eval_conds: &[&EvalCondition],
    coeff_domain: &CoeffDomain,
    point_domain: &PointDomain,
    param_vars: &VarOrder,
) -> SystemSolveOutcome {
    let mut checks = Vec::new();
    let param_bind = ExprBindings::params_only(param_vars);

    for cond in eval_conds {
        for item in &cond.evaluations {
            let err = match coeff_domain {
                CoeffDomain::Q => Poly::from_expr_q(&item.expr, &param_bind).err(),
                CoeffDomain::Z
                    if !matches!(
                        point_domain,
                        PointDomain::IntegerPoints | PointDomain::UniversalRing
                    ) =>
                {
                    Poly::from_expr_q(&item.expr, &param_bind).err()
                }
                CoeffDomain::Z => Poly::from_expr_z(&item.expr, &param_bind).err(),
                CoeffDomain::Fp(m) => Poly::from_expr_fp(&item.expr, &param_bind, m).err(),
            };
            if let Some(e) = err {
                let reason = map_algebra_silence(e);
                checks.push(ApplicabilityCheck::failed(
                    "evaluation_map_well_formed",
                    MathClause::G140E1E2,
                    reason.code(),
                ));
                return undetermined_system(checks, vec![], reason);
            }
        }
    }

    match coeff_domain {
        CoeffDomain::Fp(modulus) => solve_fp_system(
            obligations,
            extra_param_eqs,
            eval_conds,
            modulus,
            point_domain,
            param_vars,
            checks,
        ),
        CoeffDomain::Z => solve_z_system(
            obligations,
            extra_param_eqs,
            eval_conds,
            point_domain,
            param_vars,
            checks,
        ),
        CoeffDomain::Q => solve_q_system(
            obligations,
            extra_param_eqs,
            eval_conds,
            point_domain,
            param_vars,
            false,
            checks,
        ),
    }
}

fn solve_fp_system(
    obligations: &[PreservationObligation],
    extra_param_eqs: &[PolyExpr],
    eval_conds: &[&EvalCondition],
    modulus: &BigUint,
    point_domain: &PointDomain,
    param_vars: &VarOrder,
    mut checks: Vec<ApplicabilityCheck>,
) -> SystemSolveOutcome {
    if *point_domain != PointDomain::FiniteFieldPoints(modulus.clone()) {
        let reason = SilenceReason::ApplicabilityConditionNotMet {
            condition: "point_domain_matches_coeff_domain".to_owned(),
            detail: format!("point domain `{point_domain}` cannot be decided over Fp({modulus})"),
        };
        checks.push(ApplicabilityCheck::failed(
            "fp_point_domain_exact",
            MathClause::G141D4,
            reason.code(),
        ));
        return undetermined_system(checks, vec![], reason);
    }

    let param_bind = ExprBindings::params_only(param_vars);
    let mut eqs_fp = Vec::new();
    let Some(fp_zero) = FpElem::zero(modulus.clone()) else {
        return undetermined_system(
            checks,
            vec![],
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "valid_fp_modulus".to_owned(),
                detail: format!("modulus {modulus} is below 2"),
            },
        );
    };
    for ob in obligations {
        if !ob.source_laws.is_empty() {
            if param_vars.is_empty() {
                match decide_fp_quotient_exact(ob, modulus) {
                    Ok(Some(true)) => continue,
                    Ok(Some(false)) => {
                        eqs_fp.push(Poly::one(0, fp_zero.clone()));
                        continue;
                    }
                    Ok(None) => {
                        let reason = SilenceReason::QuotientIdealOutOfScope {
                            detail: "nonlinear multi-generator quotient state-law membership over F_p is out of scope".to_owned(),
                        };
                        checks.push(ApplicabilityCheck::failed(
                            "fp_quotient_out_of_scope",
                            MathClause::G141D4,
                            reason.code(),
                        ));
                        return undetermined_system(checks, vec![], reason);
                    }
                    Err(reason) => return undetermined_system(checks, vec![], reason),
                }
            }
            let reason = SilenceReason::QuotientIdealOutOfScope {
                detail: "parametric quotient state-law stratification over F_p is out of scope"
                    .to_owned(),
            };
            checks.push(ApplicabilityCheck::failed(
                "fp_quotient_out_of_scope",
                MathClause::G141D4,
                reason.code(),
            ));
            return undetermined_system(checks, vec![], reason);
        }
        if let Err(reason) = extract_obligation_ambient_eqs(
            ob,
            param_vars,
            |e, b| Poly::from_expr_fp(e, b, modulus),
            &mut eqs_fp,
        ) {
            return undetermined_system(checks, vec![], reason);
        }
    }

    let (ex_eqs, invs_fp) =
        match collect_eval_and_extra(extra_param_eqs, eval_conds, &param_bind, |e, b| {
            Poly::from_expr_fp(e, b, modulus)
        }) {
            Ok(pair) => pair,
            Err(r) => return undetermined_system(checks, vec![], r),
        };
    eqs_fp.extend(ex_eqs);

    let residual_display = display_polys(&eqs_fp, param_vars);
    match solve_fp_enumeration(
        &eqs_fp,
        &invs_fp,
        param_vars.len(),
        modulus,
        crate::limits::active_limits().max_fp_points,
    ) {
        Ok(res) => {
            checks.push(ApplicabilityCheck::passed(
                "fp_finite_enumeration_complete",
                MathClause::G141D4,
            ));
            if let Some(first) = res.solutions.first() {
                let assignments = param_vars
                    .vars()
                    .iter()
                    .zip(first)
                    .map(|(n, v)| (n.clone(), v.value().to_string()))
                    .collect();
                SystemSolveOutcome {
                    verdict: Verdict::Established,
                    checks,
                    residual_display,
                    empty_witness: None,
                    witness: Some(ParamWitness::FpPoint {
                        point: first.clone(),
                        modulus: modulus.clone(),
                        assignments,
                    }),
                }
            } else {
                refuted_system(checks, residual_display, None)
            }
        }
        Err(reason) => undetermined_system(checks, residual_display, reason),
    }
}

/// 0 パラメータの `Fp` 商環所属義務 `target in (source_laws)` を
/// 線形ピボット消去と Grevlex 多変数除算で厳密判定する（単元非判定の多生成元非線形系は `Ok(None)` で沈黙）。
pub(crate) fn decide_fp_quotient_exact(
    ob: &PreservationObligation,
    modulus: &BigUint,
) -> Result<Option<bool>, SilenceReason> {
    let n = ob.state_vars.len() + ob.arg_vars.len();
    let (_, bindings) = ExprBindings::from_slices(&ob.state_vars, &ob.arg_vars, &[])
        .map_err(map_algebra_silence)?;
    let mut cur_target =
        Poly::from_expr_fp(&ob.target, &bindings, modulus).map_err(map_algebra_silence)?;
    let mut cur_laws: Vec<Poly<FpElem>> = Vec::with_capacity(ob.source_laws.len());
    for l in &ob.source_laws {
        let p = Poly::from_expr_fp(l, &bindings, modulus).map_err(map_algebra_silence)?;
        if !p.is_zero() {
            cur_laws.push(p);
        }
    }
    if cur_laws
        .iter()
        .any(|l| l.is_constant() && l.constant_value().inv().is_some())
    {
        return Ok(Some(true));
    }

    eliminate_unit_affine_laws(n, &mut cur_target, &mut cur_laws, |c| {
        c.inv().map(|inv| inv.neg_elem())
    })?;

    if cur_laws
        .iter()
        .any(|l| l.is_constant() && l.constant_value().inv().is_some())
    {
        return Ok(Some(true));
    }
    if cur_laws.is_empty() {
        return Ok(Some(cur_target.is_zero()));
    }
    if cur_target.is_zero() {
        return Ok(Some(true));
    }

    let Some(rem) = multivariate_div_rem_fp(&cur_target, &cur_laws, 4_096)? else {
        return Ok(None);
    };
    if rem.is_zero() {
        return Ok(Some(true));
    }
    if cur_laws.len() == 1
        && cur_laws[0]
            .leading_term(MonomialOrder::Grevlex)
            .is_some_and(|(_, lc)| lc.inv().is_some())
    {
        return Ok(Some(false));
    }
    Ok(None)
}

fn multivariate_div_rem_fp(
    target: &Poly<FpElem>,
    divisors: &[Poly<FpElem>],
    max_steps: usize,
) -> Result<Option<Poly<FpElem>>, SilenceReason> {
    let mut p = target.clone();
    let mut rem = Poly::zero(target.num_vars(), target.zero_coeff().clone());
    let mut steps = 0usize;
    while !p.is_zero() {
        steps += 1;
        if steps > max_steps {
            return Ok(None);
        }
        let Some((lm_p, lc_p)) = p.leading_term(MonomialOrder::Grevlex) else {
            break;
        };
        let lm_p = lm_p.clone();
        let lc_p = lc_p.clone();
        let mut reduced = false;
        for g in divisors {
            let Some((lm_g, lc_g)) = g.leading_term(MonomialOrder::Grevlex) else {
                continue;
            };
            if let Some(quot_m) = lm_p.div_exact(lm_g) {
                let Some(inv) = lc_g.inv() else {
                    return Ok(None);
                };
                let Some(factor) = lc_p.mul_checked(&inv) else {
                    return Err(SilenceReason::ApplicabilityConditionNotMet {
                        condition: "fp_ring_match".to_owned(),
                        detail: "coefficient modulus mismatch during Fp division".to_owned(),
                    });
                };
                p.checked_sub_mul_term_assign(g, &quot_m, &factor)
                    .map_err(map_algebra_silence)?;
                reduced = true;
                break;
            }
        }
        if !reduced {
            p.remove_term(&lm_p);
            rem.add_term(lm_p, lc_p);
        }
    }
    Ok(Some(rem))
}

/// 0 パラメータの `Z` 商環所属義務 `target in (source_laws)` が単位ピボット代入・整数 cofactor で厳密判定できるか検査する。
pub(crate) fn decide_z_quotient_unit_safe(
    ob: &PreservationObligation,
    param_vars: &VarOrder,
) -> Result<Option<bool>, SilenceReason> {
    if !param_vars.is_empty() {
        return Ok(None);
    }
    let (_, bindings) = ExprBindings::from_slices(&ob.state_vars, &ob.arg_vars, &[])
        .map_err(map_algebra_silence)?;
    let n = ob.state_vars.len() + ob.arg_vars.len();
    let var_names: Vec<String> = ob.state_vars.iter().chain(&ob.arg_vars).cloned().collect();
    let var_order = VarOrder::new(var_names).map_err(map_algebra_silence)?;

    let mut cur_target = Poly::from_expr_z(&ob.target, &bindings).map_err(map_algebra_silence)?;
    let mut cur_laws: Vec<Poly<BigInt>> = Vec::with_capacity(ob.source_laws.len());
    for l in &ob.source_laws {
        let p = Poly::from_expr_z(l, &bindings).map_err(map_algebra_silence)?;
        if !p.is_zero() {
            cur_laws.push(p);
        }
    }

    eliminate_unit_affine_laws(n, &mut cur_target, &mut cur_laws, |c| {
        c.abs().is_one().then(|| -c)
    })?;

    if cur_laws.is_empty() {
        return Ok(Some(cur_target.is_zero()));
    }
    if cur_target.is_zero() {
        return Ok(Some(true));
    }

    let laws_q: Vec<Poly<Rat>> = cur_laws.iter().map(lift_z_to_q).collect();
    let target_q = lift_z_to_q(&cur_target);
    let gb = GroebnerBasis::compute(&laws_q, var_order, MonomialOrder::Grevlex)
        .map_err(map_algebra_silence)?;
    let mem = gb.membership(&target_q).map_err(map_algebra_silence)?;
    if mem.is_member {
        // 全 cofactor が整数多項式なら I·Z[x] 所属が確実に成り立つ。分母がある場合は Z-torsion 境界で保留する。
        return Ok(mem
            .cofactors
            .iter()
            .all(|c| c.terms().values().all(|r| r.den().is_one()))
            .then_some(true));
    }
    // I·Z[x] ⊆ I·Q[x] のため、Q 上での非所属は Z 上での非所属を厳密に含意する。
    Ok(Some(false))
}

fn eliminate_unit_affine_laws<C: RingCoeff>(
    num_vars: usize,
    cur_target: &mut Poly<C>,
    cur_laws: &mut Vec<Poly<C>>,
    unit_neg_inv: impl Fn(&C) -> Option<C>,
) -> Result<(), SilenceReason> {
    let mut changed = true;
    while changed && !cur_laws.is_empty() {
        changed = false;
        let found = cur_laws.iter().enumerate().find_map(|(idx, law)| {
            if !law.is_affine() {
                return None;
            }
            (0..num_vars).find_map(|v| {
                let c = affine_linear_coeff(law, v)?;
                let neg_inv = unit_neg_inv(&c)?;
                let mut rhs = Poly::zero(num_vars, law.zero_coeff().clone());
                for (m, coeff) in law.terms() {
                    if m.exps()[v] == 0 {
                        rhs.add_term(m.clone(), neg_inv.mul_ref(coeff));
                    }
                }
                Some((idx, v, rhs))
            })
        });
        if let Some((idx, v, rhs)) = found {
            changed = true;
            cur_laws.remove(idx);
            *cur_target = substitute_single_var(cur_target, v, &rhs)?;
            let mut next = Vec::with_capacity(cur_laws.len());
            for l in cur_laws.drain(..) {
                let sl = substitute_single_var(&l, v, &rhs)?;
                if !sl.is_zero() {
                    next.push(sl);
                }
            }
            *cur_laws = next;
        }
    }
    Ok(())
}

fn extract_obligation_ambient_eqs<C: RingCoeff>(
    ob: &PreservationObligation,
    param_vars: &VarOrder,
    parse_expr: impl FnOnce(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
    out: &mut Vec<Poly<C>>,
) -> Result<(), SilenceReason> {
    let Ok((_, ob_bind)) =
        ExprBindings::from_slices(&ob.state_vars, &ob.arg_vars, param_vars.vars())
    else {
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "binding_well_formed".to_owned(),
            detail: "failed to construct bindings".to_owned(),
        });
    };
    let p = parse_expr(&ob.target, &ob_bind).map_err(map_algebra_silence)?;
    let sa = ob.state_vars.len() + ob.arg_vars.len();
    out.extend(
        extract_ambient_param_coeffs(&p, sa, param_vars.len())
            .into_iter()
            .filter(|c| !c.is_zero()),
    );
    Ok(())
}

fn affine_linear_coeff<C: RingCoeff>(poly: &Poly<C>, var: usize) -> Option<C> {
    poly.terms()
        .iter()
        .find(|(m, _)| m.total_degree() == 1 && m.exps()[var] == 1)
        .map(|(_, c)| c.clone())
}

fn substitute_single_var<C: RingCoeff>(
    poly: &Poly<C>,
    var: usize,
    rhs: &Poly<C>,
) -> Result<Poly<C>, SilenceReason> {
    let mut acc = Poly::zero(poly.num_vars(), poly.zero_coeff().clone());
    for (mono, coeff) in poly.terms() {
        let mut exps = mono.exps().to_vec();
        let power = exps[var];
        exps[var] = 0;
        let mut term = Poly::zero(poly.num_vars(), poly.zero_coeff().clone());
        term.add_term(Monomial::from_exps(exps), coeff.clone());
        for _ in 0..power {
            term = term.checked_mul(rhs).map_err(map_algebra_silence)?;
        }
        acc = acc.add(&term);
    }
    Ok(acc)
}

pub(crate) fn lift_z_to_q(poly: &Poly<BigInt>) -> Poly<Rat> {
    let mut out = Poly::zero(poly.num_vars(), Rat::zero());
    for (m, c) in poly.terms() {
        out.add_term(m.clone(), Rat::from_int(c.clone()));
    }
    out
}

fn solve_z_system(
    obligations: &[PreservationObligation],
    extra_param_eqs: &[PolyExpr],
    eval_conds: &[&EvalCondition],
    point_domain: &PointDomain,
    param_vars: &VarOrder,
    mut checks: Vec<ApplicabilityCheck>,
) -> SystemSolveOutcome {
    let has_source_laws = obligations.iter().any(|o| !o.source_laws.is_empty());

    if *point_domain == PointDomain::UniversalRing {
        let reason = SilenceReason::ApplicabilityConditionNotMet {
            condition: "universal_ring_solution_space_out_of_scope".to_owned(),
            detail: "UniversalRing solution-space restoration over Z cannot be approximated by rational Q-sections".to_owned(),
        };
        checks.push(ApplicabilityCheck::failed(
            "universal_ring_solution_space_out_of_scope",
            MathClause::G141D1,
            reason.code(),
        ));
        return undetermined_system(checks, vec![], reason);
    }

    if *point_domain != PointDomain::IntegerPoints {
        if has_source_laws && *point_domain != PointDomain::AlgebraicClosure {
            let reason = SilenceReason::QuotientIdealOutOfScope {
                detail: "parametric quotient state-law membership over Z (with possible Z-torsion) is out of scope; use Q or algebraic_closure".to_owned(),
            };
            checks.push(ApplicabilityCheck::failed(
                "z_quotient_out_of_scope",
                MathClause::G141D5,
                reason.code(),
            ));
            return undetermined_system(checks, vec![], reason);
        }
        return solve_q_system(
            obligations,
            extra_param_eqs,
            eval_conds,
            point_domain,
            param_vars,
            true,
            checks,
        );
    }

    if has_source_laws {
        match try_decide_unit_z_quotients(
            obligations,
            extra_param_eqs,
            eval_conds,
            param_vars,
            &mut checks,
        ) {
            Ok(Some(res)) => return res,
            Ok(None) => {}
            Err(reason) => return undetermined_system(checks, vec![], reason),
        }
        let reason = SilenceReason::QuotientIdealOutOfScope {
            detail: "parametric quotient state-law membership over Z is out of scope; use Q or algebraic_closure".to_owned(),
        };
        checks.push(ApplicabilityCheck::failed(
            "z_quotient_out_of_scope",
            MathClause::G141D5,
            reason.code(),
        ));
        return undetermined_system(checks, vec![], reason);
    }

    let param_bind = ExprBindings::params_only(param_vars);
    let mut eqs_z = Vec::new();
    for ob in obligations {
        if let Err(reason) =
            extract_obligation_ambient_eqs(ob, param_vars, Poly::from_expr_z, &mut eqs_z)
        {
            return undetermined_system(checks, vec![], reason);
        }
    }
    let (ex_eqs, invs_z) =
        match collect_eval_and_extra(extra_param_eqs, eval_conds, &param_bind, Poly::from_expr_z) {
            Ok(pair) => pair,
            Err(r) => return undetermined_system(checks, vec![], r),
        };
    eqs_z.extend(ex_eqs);
    solve_affine_or_nonlinear_z(&eqs_z, &invs_z, param_vars, checks)
}

pub(crate) fn try_decide_unit_z_quotients(
    obligations: &[PreservationObligation],
    extra_param_eqs: &[PolyExpr],
    eval_conds: &[&EvalCondition],
    param_vars: &VarOrder,
    checks: &mut Vec<ApplicabilityCheck>,
) -> Result<Option<SystemSolveOutcome>, SilenceReason> {
    if !param_vars.is_empty() {
        return Ok(None);
    }
    let param_bind = ExprBindings::params_only(param_vars);
    let (mut eqs_z, invs_z) =
        collect_eval_and_extra(extra_param_eqs, eval_conds, &param_bind, Poly::from_expr_z)?;
    for ob in obligations {
        if ob.source_laws.is_empty() {
            let (_, ob_bind) = ExprBindings::from_slices(&ob.state_vars, &ob.arg_vars, &[])
                .map_err(map_algebra_silence)?;
            let p = Poly::from_expr_z(&ob.target, &ob_bind).map_err(map_algebra_silence)?;
            if !p.is_zero() {
                eqs_z.push(Poly::one(0, BigInt::zero()));
            }
        } else {
            match decide_z_quotient_unit_safe(ob, param_vars)? {
                Some(true) => {}
                Some(false) => eqs_z.push(Poly::one(0, BigInt::zero())),
                None => return Ok(None),
            }
        }
    }
    Ok(Some(solve_affine_or_nonlinear_z(
        &eqs_z,
        &invs_z,
        param_vars,
        std::mem::take(checks),
    )))
}

pub(crate) fn solve_affine_or_nonlinear_z(
    eqs_z: &[Poly<BigInt>],
    invs_z: &[Poly<BigInt>],
    param_vars: &VarOrder,
    mut checks: Vec<ApplicabilityCheck>,
) -> SystemSolveOutcome {
    let residual_display = display_polys(eqs_z, param_vars);
    let all_affine = eqs_z.iter().all(Poly::is_affine);
    if !all_affine {
        let eqs_q: Vec<Poly<Rat>> = eqs_z.iter().map(lift_z_to_q).collect();
        let invs_q: Vec<Poly<Rat>> = invs_z.iter().map(lift_z_to_q).collect();
        if let Ok(rab) = rabinowitsch_solve(&eqs_q, &invs_q, param_vars)
            && rab.is_empty_over_closure
        {
            checks.push(ApplicabilityCheck::passed(
                "rabinowitsch_emptiness_verified",
                MathClause::G141D5,
            ));
            return refuted_system(checks, residual_display, rab.empty_witness);
        }
        let reason = SilenceReason::NonLinearRationalOrIntegerExistence {
            point_domain: PointDomain::IntegerPoints,
            detail: "general integer-point existence for nonlinear equations is out of scope"
                .to_owned(),
        };
        checks.push(ApplicabilityCheck::failed(
            "integer_point_existence_decidable",
            MathClause::G141D4,
            reason.code(),
        ));
        return undetermined_system(checks, residual_display, reason);
    }

    let Ok((mat, rhs)) = polys_to_affine_system_z(eqs_z, param_vars.len()) else {
        return undetermined_system(
            checks,
            residual_display,
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "affine_system_expected".to_owned(),
                detail: "failed to convert Z system to matrix".to_owned(),
            },
        );
    };
    match solve_affine_z(&mat, &rhs, param_vars.len()) {
        Ok(AffineSolutionZ::Inconsistent { verified: true, .. }) => {
            checks.push(ApplicabilityCheck::passed(
                "smith_normal_form_inconsistency_verified",
                MathClause::G141D4,
            ));
            refuted_system(checks, residual_display, None)
        }
        Ok(AffineSolutionZ::Consistent {
            particular,
            kernel_basis,
            verified: true,
            ..
        }) => {
            let chosen = if invs_z.is_empty() {
                Some(particular)
            } else {
                match find_witness_point_z(&particular, &kernel_basis, eqs_z, invs_z) {
                    Ok(pt) => pt,
                    Err(reason) => return undetermined_system(checks, residual_display, reason),
                }
            };
            let Some(pt) = chosen else {
                if kernel_basis.is_empty() {
                    checks.push(ApplicabilityCheck::passed(
                        "unique_integer_point_violates_open_condition",
                        MathClause::G141D4,
                    ));
                    return refuted_system(checks, residual_display, None);
                }
                return undetermined_system(
                    checks,
                    residual_display,
                    SilenceReason::NonLinearRationalOrIntegerExistence {
                        point_domain: PointDomain::IntegerPoints,
                        detail: "no integer point making invertibles units (|g|=1) verified"
                            .to_owned(),
                    },
                );
            };
            let assignments = param_vars
                .vars()
                .iter()
                .zip(&pt)
                .map(|(n, v)| (n.clone(), v.to_string()))
                .collect();
            checks.push(ApplicabilityCheck::passed(
                "smith_normal_form_solution_verified",
                MathClause::G141D4,
            ));
            SystemSolveOutcome {
                verdict: Verdict::Established,
                checks,
                residual_display,
                empty_witness: None,
                witness: Some(ParamWitness::ZPoint {
                    point: pt,
                    assignments,
                }),
            }
        }
        Ok(_) => undetermined_system(
            checks,
            residual_display,
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "smith_normal_form_verification".to_owned(),
                detail: "Smith normal form verification failed".to_owned(),
            },
        ),
        Err(e) => undetermined_system(checks, residual_display, map_algebra_silence(e)),
    }
}
