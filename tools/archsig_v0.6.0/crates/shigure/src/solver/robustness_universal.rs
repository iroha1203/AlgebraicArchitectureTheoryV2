//! 全係数移送で安定な全称条件 $\mathcal{R}(R)$・$\mathcal{R}_{\mathrm{dec}}(R)$ の判定（G-140 E5 / G-142 G3・W6）。
//!
//! Yoneda の補題により、多項式族 $U_b = \operatorname{Spec} k[u]/I_{U,b}[g^{-1}]$ 上の全 $k$-代数での成立は
//! 普遍座標環 $S_{\mathrm{univ}} = k[u, v]/(I_{U,b}, v_j g_j - 1)$ でのイデアル所属および単元性と同値である。
//! 反証時は普遍座標環反例に加え、1 変数重根での形式微分による双対数環反例も一般構成する。

use crate::algebra::{
    DEFAULT_MAX_BUCHBERGER_PAIRS, ExprBindings, FpElem, GroebnerBasis, Monomial, MonomialOrder,
    Poly, Rat, RingCoeff, VarOrder,
};
use crate::ir::family::{CheckedFamilySpec, GoodnessSpec, RealizationSpace};
use crate::ir::result::SilenceReason;
use crate::ir::result_phase3::{DualNumberCounterexample, UniversalRingStabilityResult};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::solver::context::display_polys;
use crate::solver::family_direct::substitute_preservation_pair;
use crate::solver::family_eval::{EnumCandidate, univariate_rational_roots};
use crate::solver::preservation::{
    build_preservation_obligations, extract_ambient_param_coeffs, extract_closed_residuals_fp,
    map_algebra_silence, substitute_poly_expr,
};
use num_bigint::{BigInt, BigUint};
use num_traits::Zero;
use std::collections::{BTreeMap, BTreeSet};

/// 指定候補 $c$ が全係数移送安定集合 $\mathcal{R}(R)$・確定集合 $\mathcal{R}_{\mathrm{dec}}(R)$ に属するか判定する。
pub(crate) fn evaluate_universal_ring(
    family: &CheckedFamilySpec,
    base_value: &[ScalarLit],
    candidate: &EnumCandidate,
    fiber_non_empty: bool,
) -> Result<UniversalRingStabilityResult, SilenceReason> {
    let domain = family.coeff_domain();
    let u_names = family.u_vars();
    let c_names = family.c_vars();

    let (u_eq_exprs, u_inv_exprs) = match &family.inner().realizations.space {
        RealizationSpace::PolynomialScheme {
            equations,
            invertibles,
            ..
        } => (
            equations.iter().map(|e| e.expr.clone()).collect::<Vec<_>>(),
            invertibles
                .iter()
                .map(|i| i.expr.clone())
                .collect::<Vec<_>>(),
        ),
        RealizationSpace::FiniteMembers(_) => {
            return Ok(universal_silence(SilenceReason::UniversalRingOutOfScope {
                detail: "universal base-change check requires a PolynomialScheme realization family; finite discrete enumeration is fixed over base points".to_owned(),
            }));
        }
    };

    let (good_eq_exprs, good_inv_exprs) =
        match collect_direct_residuals_in_u(family, c_names, candidate, domain) {
            Ok(pair) => pair,
            Err(SilenceReason::UniversalRingOutOfScope { detail }) => {
                return Ok(universal_silence(SilenceReason::UniversalRingOutOfScope {
                    detail,
                }));
            }
            Err(other) => return Err(other),
        };

    let mut scheme_eq_exprs = u_eq_exprs;
    for (q_expr, b_lit) in family.inner().realizations.reading_q.iter().zip(base_value) {
        scheme_eq_exprs.push(PolyExpr::diff(
            q_expr.clone(),
            PolyExpr::Const(b_lit.clone()),
        ));
    }

    match domain {
        CoeffDomain::Q => eval_universal_q(
            u_names,
            &scheme_eq_exprs,
            &u_inv_exprs,
            &good_eq_exprs,
            &good_inv_exprs,
            fiber_non_empty,
        ),
        CoeffDomain::Fp(p) => eval_universal_fp(
            u_names,
            &scheme_eq_exprs,
            &u_inv_exprs,
            &good_eq_exprs,
            &good_inv_exprs,
            p,
            fiber_non_empty,
        ),
        CoeffDomain::Z => Ok(universal_silence(SilenceReason::UniversalRingOutOfScope {
            detail: "universal base-change over arbitrary commutative Z-algebras (with possible non-flat torsion) is out of scope; use Q or Fp".to_owned(),
        })),
    }
}

fn universal_silence(reason: SilenceReason) -> UniversalRingStabilityResult {
    UniversalRingStabilityResult {
        evaluated: false,
        stable: None,
        inhabited_stable: None,
        counterexample_ring: None,
        counterexample_point: BTreeMap::new(),
        counterexample_residuals: vec![],
        dual_number_counterexample: None,
        silence_reason: Some(reason),
    }
}

fn collect_direct_residuals_in_u(
    family: &CheckedFamilySpec,
    c_names: &[String],
    candidate: &EnumCandidate,
    domain: &CoeffDomain,
) -> Result<(Vec<PolyExpr>, Vec<PolyExpr>), SilenceReason> {
    let empty = BTreeMap::new();
    let mut c_subst: BTreeMap<String, PolyExpr> = BTreeMap::new();
    for (name, sv) in c_names.iter().zip(&candidate.values) {
        c_subst.insert(name.clone(), sv.to_expr());
    }
    for u in family.u_vars() {
        c_subst.insert(u.clone(), PolyExpr::param(u));
    }

    match &family.inner().goodness {
        GoodnessSpec::Direct {
            equations,
            invertibles,
            preservation,
            raw_sequence,
        } => {
            if raw_sequence.is_some() {
                return Err(SilenceReason::UniversalRingOutOfScope {
                    detail: "raw_sequence goodness cannot be lifted uniformly over arbitrary base-change rings".to_owned(),
                });
            }
            let mut eqs: Vec<PolyExpr> = equations
                .iter()
                .map(|e| substitute_poly_expr(&e.expr, &empty, &empty, &c_subst))
                .collect();
            let invs: Vec<PolyExpr> = invertibles
                .iter()
                .map(|i| substitute_poly_expr(&i.expr, &empty, &empty, &c_subst))
                .collect();
            if let Some(pres_src) = preservation {
                let (pair, _) = substitute_preservation_pair(pres_src, &c_subst)?;
                let obligations = build_preservation_obligations(&pair)?;
                if obligations.iter().any(|o| !o.source_laws.is_empty()) {
                    return Err(SilenceReason::UniversalRingOutOfScope {
                        detail: "quotient state-law preservation over arbitrary non-reduced base-change algebras is out of scope".to_owned(),
                    });
                }
                let u_vars = VarOrder::new(family.u_vars().to_vec()).map_err(map_algebra_silence)?;
                match domain {
                    CoeffDomain::Q => {
                        for ob in &obligations {
                            let (_, bindings) = ExprBindings::from_slices(
                                &ob.state_vars,
                                &ob.arg_vars,
                                family.u_vars(),
                            )
                            .map_err(map_algebra_silence)?;
                            let poly =
                                Poly::from_expr_q(&ob.target, &bindings).map_err(map_algebra_silence)?;
                            let sa = ob.state_vars.len() + ob.arg_vars.len();
                            for p in extract_ambient_param_coeffs(&poly, sa, family.u_vars().len()) {
                                eqs.push(poly_to_expr_q(&p, &u_vars));
                            }
                        }
                    }
                    CoeffDomain::Fp(m) => {
                        let Some(res) =
                            extract_closed_residuals_fp(&obligations, family.u_vars(), m)?
                        else {
                            return Err(SilenceReason::UniversalRingOutOfScope {
                                detail: "preservation source requires quotient stratification over Fp"
                                    .to_owned(),
                            });
                        };
                        for p in res {
                            eqs.push(poly_to_expr_fp(&p, &u_vars, m));
                        }
                    }
                    CoeffDomain::Z => {
                        return Err(SilenceReason::UniversalRingOutOfScope {
                            detail: "preservation residuals over Z universal algebras are out of scope"
                                .to_owned(),
                        });
                    }
                }
            }
            Ok((eqs, invs))
        }
        GoodnessSpec::Existential { .. } => Err(SilenceReason::UniversalRingOutOfScope {
            detail: "existential goodness universal base-change requires full fiber morphisms; only direct goodness is checked universally".to_owned(),
        }),
    }
}

fn poly_to_expr_q(poly: &Poly<Rat>, vars: &VarOrder) -> PolyExpr {
    let mut acc: Option<PolyExpr> = None;
    for (mono, coeff) in poly.terms() {
        let mut term = PolyExpr::constant(coeff.to_scalar_lit());
        for (idx, &e) in mono.exps().iter().enumerate() {
            if e > 0 {
                let var = PolyExpr::param(&vars.vars()[idx]);
                let factor = if e == 1 { var } else { PolyExpr::pow(var, e) };
                term = PolyExpr::prod(term, factor);
            }
        }
        acc = Some(match acc {
            None => term,
            Some(prev) => PolyExpr::sum(prev, term),
        });
    }
    acc.unwrap_or_else(|| PolyExpr::constant(Rat::zero().to_scalar_lit()))
}

fn poly_to_expr_fp(poly: &Poly<FpElem>, vars: &VarOrder, modulus: &BigUint) -> PolyExpr {
    let mut acc: Option<PolyExpr> = None;
    for (mono, coeff) in poly.terms() {
        let mut term = PolyExpr::constant(ScalarLit::Fp {
            value: coeff.value().clone(),
            modulus: modulus.clone(),
        });
        for (idx, &e) in mono.exps().iter().enumerate() {
            if e > 0 {
                let var = PolyExpr::param(&vars.vars()[idx]);
                let factor = if e == 1 { var } else { PolyExpr::pow(var, e) };
                term = PolyExpr::prod(term, factor);
            }
        }
        acc = Some(match acc {
            None => term,
            Some(prev) => PolyExpr::sum(prev, term),
        });
    }
    acc.unwrap_or_else(|| {
        PolyExpr::constant(ScalarLit::Fp {
            value: BigUint::zero(),
            modulus: modulus.clone(),
        })
    })
}

fn build_ext_vars(u_names: &[String], num_invs: usize) -> Result<VarOrder, SilenceReason> {
    let mut names = u_names.to_vec();
    for j in 0..num_invs {
        let mut cand = format!("__loc_{j}");
        while names.contains(&cand) {
            cand.push('_');
        }
        names.push(cand);
    }
    VarOrder::new(names).map_err(map_algebra_silence)
}

fn describe_coord_ring(base_label: &str, u_names: &[String], ideal_disp: &[String]) -> String {
    let vars_str = u_names.join(", ");
    if ideal_disp.is_empty() {
        format!("{base_label}[{vars_str}]")
    } else {
        format!("{base_label}[{vars_str}]/({})", ideal_disp.join(", "))
    }
}

fn eval_universal_q(
    u_names: &[String],
    scheme_eq_exprs: &[PolyExpr],
    u_inv_exprs: &[PolyExpr],
    good_eq_exprs: &[PolyExpr],
    good_inv_exprs: &[PolyExpr],
    fiber_non_empty: bool,
) -> Result<UniversalRingStabilityResult, SilenceReason> {
    let ext_vars = build_ext_vars(u_names, u_inv_exprs.len())?;
    let u_only_vars = VarOrder::new(u_names.to_vec()).map_err(map_algebra_silence)?;
    let ext_bind = ExprBindings::params_only(&ext_vars);
    let u_len = u_names.len();

    let mut gens: Vec<Poly<Rat>> = scheme_eq_exprs
        .iter()
        .map(|e| Poly::from_expr_q(e, &ext_bind))
        .collect::<Result<_, _>>()
        .map_err(map_algebra_silence)?;
    let one = Poly::one(ext_vars.len(), Rat::zero());
    for (j, inv_e) in u_inv_exprs.iter().enumerate() {
        let loc_v = Poly::var(ext_vars.len(), u_len + j, Rat::zero());
        let g_p = Poly::from_expr_q(inv_e, &ext_bind).map_err(map_algebra_silence)?;
        gens.push(
            loc_v
                .checked_mul(&g_p)
                .map_err(map_algebra_silence)?
                .sub(&one),
        );
    }

    let gb = GroebnerBasis::compute(&gens, ext_vars.clone(), MonomialOrder::Grevlex)
        .map_err(map_algebra_silence)?;
    if gb.contains_one() {
        return Ok(UniversalRingStabilityResult {
            evaluated: true,
            stable: Some(true),
            inhabited_stable: Some(false),
            counterexample_ring: None,
            counterexample_point: BTreeMap::new(),
            counterexample_residuals: vec![],
            dual_number_counterexample: None,
            silence_reason: None,
        });
    }

    let mut nonzero_residuals = Vec::new();
    for eq_e in good_eq_exprs {
        let p = Poly::from_expr_q(eq_e, &ext_bind).map_err(map_algebra_silence)?;
        let rem = gb.normal_form(&p).map_err(map_algebra_silence)?;
        if !rem.is_zero() {
            nonzero_residuals.push(rem.display(&ext_vars, MonomialOrder::Grevlex));
        }
    }
    for inv_e in good_inv_exprs {
        let h = Poly::from_expr_q(inv_e, &ext_bind).map_err(map_algebra_silence)?;
        let mut with_h = gens.clone();
        with_h.push(h.clone());
        let h_gb = GroebnerBasis::compute(&with_h, ext_vars.clone(), MonomialOrder::Grevlex)
            .map_err(map_algebra_silence)?;
        if !h_gb.contains_one() {
            nonzero_residuals.push(format!(
                "non_unit({})",
                h.display(&ext_vars, MonomialOrder::Grevlex)
            ));
        }
    }

    if nonzero_residuals.is_empty() {
        return Ok(UniversalRingStabilityResult {
            evaluated: true,
            stable: Some(true),
            inhabited_stable: Some(fiber_non_empty),
            counterexample_ring: None,
            counterexample_point: BTreeMap::new(),
            counterexample_residuals: vec![],
            dual_number_counterexample: None,
            silence_reason: None,
        });
    }

    let ideal_disp = display_polys(&gens, &ext_vars);
    let ring_desc = describe_coord_ring("Q", u_names, &ideal_disp);
    let ce_point: BTreeMap<String, String> =
        u_names.iter().map(|n| (n.clone(), n.clone())).collect();

    // 1 変数重根における双対数環 k[eps]/(eps^2) 反例の一般自動構成（局所化 g_U(a) != 0 も検査）。
    let dual_ce = if u_len == 1 {
        let u_bind = ExprBindings::params_only(&u_only_vars);
        let u_gens: Vec<Poly<Rat>> = scheme_eq_exprs
            .iter()
            .map(|e| Poly::from_expr_q(e, &u_bind))
            .collect::<Result<_, _>>()
            .map_err(map_algebra_silence)?;
        let u_loc_invs: Vec<Poly<Rat>> = u_inv_exprs
            .iter()
            .map(|e| Poly::from_expr_q(e, &u_bind))
            .collect::<Result<_, _>>()
            .map_err(map_algebra_silence)?;
        let u_res: Vec<Poly<Rat>> = good_eq_exprs
            .iter()
            .map(|e| Poly::from_expr_q(e, &u_bind))
            .collect::<Result<_, _>>()
            .map_err(map_algebra_silence)?;
        let u_invs: Vec<Poly<Rat>> = good_inv_exprs
            .iter()
            .map(|e| Poly::from_expr_q(e, &u_bind))
            .collect::<Result<_, _>>()
            .map_err(map_algebra_silence)?;
        derive_univariate_dual_counterexample(&u_names[0], &u_gens, &u_loc_invs, &u_res, &u_invs)?
    } else {
        None
    };

    Ok(UniversalRingStabilityResult {
        evaluated: true,
        stable: Some(false),
        inhabited_stable: Some(false),
        counterexample_ring: Some(ring_desc),
        counterexample_point: ce_point,
        counterexample_residuals: nonzero_residuals,
        dual_number_counterexample: dual_ce,
        silence_reason: None,
    })
}

fn poly_to_dense_q(p: &Poly<Rat>) -> Vec<Rat> {
    if p.is_zero() {
        return vec![];
    }
    let deg = p.total_degree() as usize;
    let mut coeffs = vec![Rat::zero(); deg + 1];
    for (m, c) in p.terms() {
        coeffs[m.exps()[0] as usize] = c.clone();
    }
    while coeffs.last().is_some_and(Rat::is_zero) {
        coeffs.pop();
    }
    coeffs
}

fn dense_deriv_q(p: &[Rat]) -> Vec<Rat> {
    if p.len() <= 1 {
        return vec![];
    }
    let mut out: Vec<Rat> = p
        .iter()
        .enumerate()
        .skip(1)
        .map(|(k, c)| c * &Rat::from_int(k as i64))
        .collect();
    while out.last().is_some_and(Rat::is_zero) {
        out.pop();
    }
    out
}

fn dense_rem_q(a: &[Rat], b: &[Rat]) -> Vec<Rat> {
    let mut r = a.to_vec();
    while r.last().is_some_and(Rat::is_zero) {
        r.pop();
    }
    if b.is_empty() {
        return r;
    }
    let b_deg = b.len() - 1;
    let b_lc_inv = b[b_deg].inv().expect("leading coeff nonzero");
    while r.len() > b_deg {
        let shift = (r.len() - 1) - b_deg;
        let factor = r.last().expect("nonempty") * &b_lc_inv;
        for i in 0..=b_deg {
            let sub = &factor * &b[i];
            r[i + shift] = &r[i + shift] - &sub;
        }
        while r.last().is_some_and(Rat::is_zero) {
            r.pop();
        }
    }
    r
}

fn dense_gcd_q(mut a: Vec<Rat>, mut b: Vec<Rat>) -> Vec<Rat> {
    while !b.is_empty() {
        let r = dense_rem_q(&a, &b);
        a = b;
        b = r;
    }
    if let Some(lc) = a.last().cloned()
        && let Some(inv) = lc.inv()
    {
        for c in &mut a {
            *c = &*c * &inv;
        }
    }
    a
}

fn dense_eval_q(p: &[Rat], x: &Rat) -> Rat {
    let mut acc = Rat::zero();
    for c in p.iter().rev() {
        acc = &(&acc * x) + c;
    }
    acc
}

fn format_dual(c0: &Rat, c1: &Rat) -> String {
    let s0 = c0.to_string();
    let s1 = c1.to_string();
    match (c0.is_zero(), c1.is_zero()) {
        (true, true) => "0".to_owned(),
        (false, true) => s0,
        (true, false) => {
            if c1.is_one() {
                "eps".to_owned()
            } else if c1.is_neg_one() {
                "-eps".to_owned()
            } else {
                format!("{s1}*eps")
            }
        }
        (false, false) => {
            if c1.is_one() {
                format!("{s0} + eps")
            } else if c1.is_neg_one() {
                format!("{s0} - eps")
            } else if let Some(abs1) = s1.strip_prefix('-') {
                format!("{s0} - {abs1}*eps")
            } else {
                format!("{s0} + {s1}*eps")
            }
        }
    }
}

fn derive_univariate_dual_counterexample(
    var_name: &str,
    u_gens: &[Poly<Rat>],
    u_loc_invs: &[Poly<Rat>],
    good_eqs: &[Poly<Rat>],
    good_invs: &[Poly<Rat>],
) -> Result<Option<DualNumberCounterexample>, SilenceReason> {
    let dense_gens: Vec<Vec<Rat>> = u_gens
        .iter()
        .filter(|g| !g.is_zero())
        .map(poly_to_dense_q)
        .collect();
    if dense_gens.is_empty() {
        return Ok(None);
    }
    let mut g_all = dense_gens[0].clone();
    for next in &dense_gens[1..] {
        g_all = dense_gcd_q(g_all, next.clone());
    }
    if g_all.len() <= 2 {
        return Ok(None);
    }
    let dg = dense_deriv_q(&g_all);
    let rep = dense_gcd_q(g_all, dg);
    if rep.len() <= 1 {
        return Ok(None);
    }

    let mut rep_poly = Poly::zero(1, Rat::zero());
    for (deg, c) in rep.iter().enumerate() {
        if !c.is_zero() {
            rep_poly.add_term(Monomial::from_exps(vec![deg as u32]), c.clone());
        }
    }
    let (roots, _) = univariate_rational_roots(&rep_poly)?;
    for a in roots {
        if u_loc_invs
            .iter()
            .any(|g| dense_eval_q(&poly_to_dense_q(g), &a).is_zero())
        {
            continue;
        }
        let mut nonzero = Vec::new();
        for f in good_eqs {
            let df = poly_to_dense_q(f);
            let f_deriv = dense_deriv_q(&df);
            let c0 = dense_eval_q(&df, &a);
            let c1 = dense_eval_q(&f_deriv, &a);
            if !c0.is_zero() || !c1.is_zero() {
                nonzero.push(format_dual(&c0, &c1));
            }
        }
        for h in good_invs {
            let dh = poly_to_dense_q(h);
            let c0 = dense_eval_q(&dh, &a);
            if c0.is_zero() {
                let c1 = dense_eval_q(&dense_deriv_q(&dh), &a);
                nonzero.push(format!("non_unit({})", format_dual(&c0, &c1)));
            }
        }
        if !nonzero.is_empty() {
            return Ok(Some(DualNumberCounterexample {
                ring_description: "Q[eps]/(eps^2)".to_owned(),
                assignments: BTreeMap::from([(var_name.to_owned(), format_dual(&a, &Rat::one()))]),
                nonzero_residuals: nonzero,
            }));
        }
    }
    Ok(None)
}

fn eval_universal_fp(
    u_names: &[String],
    scheme_eq_exprs: &[PolyExpr],
    u_inv_exprs: &[PolyExpr],
    good_eq_exprs: &[PolyExpr],
    good_inv_exprs: &[PolyExpr],
    modulus: &BigUint,
    fiber_non_empty: bool,
) -> Result<UniversalRingStabilityResult, SilenceReason> {
    let ext_vars = build_ext_vars(u_names, u_inv_exprs.len())?;
    let ext_bind = ExprBindings::params_only(&ext_vars);
    let u_len = u_names.len();

    let mut gens: Vec<Poly<FpElem>> = scheme_eq_exprs
        .iter()
        .map(|e| Poly::from_expr_fp(e, &ext_bind, modulus))
        .collect::<Result<_, _>>()
        .map_err(map_algebra_silence)?;
    let zero_fp = FpElem::from_checked_prime(BigInt::zero(), modulus.clone());
    let one = Poly::one(ext_vars.len(), zero_fp.clone());
    for (j, inv_e) in u_inv_exprs.iter().enumerate() {
        let loc_v = Poly::var(ext_vars.len(), u_len + j, zero_fp.clone());
        let g_p = Poly::from_expr_fp(inv_e, &ext_bind, modulus).map_err(map_algebra_silence)?;
        gens.push(
            loc_v
                .checked_mul(&g_p)
                .map_err(map_algebra_silence)?
                .sub(&one),
        );
    }

    let gb = fp_groebner(&gens, MonomialOrder::Grevlex)?;
    if fp_basis_contains_one(&gb, MonomialOrder::Grevlex) {
        return Ok(UniversalRingStabilityResult {
            evaluated: true,
            stable: Some(true),
            inhabited_stable: Some(false),
            counterexample_ring: None,
            counterexample_point: BTreeMap::new(),
            counterexample_residuals: vec![],
            dual_number_counterexample: None,
            silence_reason: None,
        });
    }

    let mut nonzero_residuals = Vec::new();
    for eq_e in good_eq_exprs {
        let p = Poly::from_expr_fp(eq_e, &ext_bind, modulus).map_err(map_algebra_silence)?;
        let rem = fp_reduce(&p, &gb, MonomialOrder::Grevlex)?;
        if !rem.is_zero() {
            nonzero_residuals.push(rem.display(&ext_vars, MonomialOrder::Grevlex));
        }
    }
    for inv_e in good_inv_exprs {
        let h = Poly::from_expr_fp(inv_e, &ext_bind, modulus).map_err(map_algebra_silence)?;
        let mut with_h = gens.clone();
        with_h.push(h.clone());
        let h_gb = fp_groebner(&with_h, MonomialOrder::Grevlex)?;
        if !fp_basis_contains_one(&h_gb, MonomialOrder::Grevlex) {
            nonzero_residuals.push(format!(
                "non_unit({})",
                h.display(&ext_vars, MonomialOrder::Grevlex)
            ));
        }
    }

    if nonzero_residuals.is_empty() {
        return Ok(UniversalRingStabilityResult {
            evaluated: true,
            stable: Some(true),
            inhabited_stable: Some(fiber_non_empty),
            counterexample_ring: None,
            counterexample_point: BTreeMap::new(),
            counterexample_residuals: vec![],
            dual_number_counterexample: None,
            silence_reason: None,
        });
    }

    let ideal_disp = display_polys(&gens, &ext_vars);
    let ring_desc = describe_coord_ring(&format!("Fp({modulus})"), u_names, &ideal_disp);
    let ce_point: BTreeMap<String, String> =
        u_names.iter().map(|n| (n.clone(), n.clone())).collect();
    Ok(UniversalRingStabilityResult {
        evaluated: true,
        stable: Some(false),
        inhabited_stable: Some(false),
        counterexample_ring: Some(ring_desc),
        counterexample_point: ce_point,
        counterexample_residuals: nonzero_residuals,
        dual_number_counterexample: None,
        silence_reason: None,
    })
}

fn fp_make_monic(poly: &Poly<FpElem>, order: MonomialOrder) -> Poly<FpElem> {
    let Some((_, lc)) = poly.leading_term(order) else {
        return poly.clone();
    };
    if lc.is_one() {
        return poly.clone();
    }
    let inv = lc.inv().expect("leading coefficient in Fp is nonzero");
    poly.scale(&inv)
}

fn fp_basis_contains_one(basis: &[Poly<FpElem>], order: MonomialOrder) -> bool {
    basis
        .iter()
        .any(|p| p.leading_term(order).is_some_and(|(m, _)| m.is_one()))
}

fn fp_reduce(
    target: &Poly<FpElem>,
    basis: &[Poly<FpElem>],
    order: MonomialOrder,
) -> Result<Poly<FpElem>, SilenceReason> {
    let mut cur = target.clone();
    let mut rem = Poly::zero(target.num_vars(), target.zero_coeff().clone());
    while let Some((lm_cur, lc_cur)) = cur.leading_term(order) {
        let lm_cur = lm_cur.clone();
        let lc_cur = lc_cur.clone();
        let mut divided = false;
        for g in basis {
            if let Some((lm_g, lc_g)) = g.leading_term(order)
                && let Some(shift) = lm_cur.div_exact(lm_g)
            {
                let inv_g = lc_g.inv().expect("nonzero divisor lc");
                let factor = lc_cur.mul_ref(&inv_g);
                cur.checked_sub_mul_term_assign(g, &shift, &factor)
                    .map_err(map_algebra_silence)?;
                divided = true;
                break;
            }
        }
        if !divided {
            cur.remove_term(&lm_cur);
            rem.add_term(lm_cur, lc_cur);
        }
    }
    Ok(rem)
}

fn fp_groebner(
    generators: &[Poly<FpElem>],
    order: MonomialOrder,
) -> Result<Vec<Poly<FpElem>>, SilenceReason> {
    let mut basis: Vec<Poly<FpElem>> = Vec::new();
    let mut lms: Vec<Monomial> = Vec::new();
    for g in generators {
        if g.is_zero() {
            continue;
        }
        let m = fp_make_monic(g, order);
        let Some((lm, _)) = m.leading_term(order) else {
            continue;
        };
        let lm = lm.clone();
        if lm.is_one() {
            return Ok(vec![m]);
        }
        lms.push(lm);
        basis.push(m);
    }
    let mut pairs: Vec<(usize, usize)> = Vec::new();
    for i in 0..basis.len() {
        for j in (i + 1)..basis.len() {
            pairs.push((i, j));
        }
    }
    let mut processed = 0usize;
    let mut seen: BTreeSet<(usize, usize)> = BTreeSet::new();
    while let Some((i, j)) = pairs.pop() {
        let key = if i < j { (i, j) } else { (j, i) };
        if !seen.insert(key) {
            continue;
        }
        processed += 1;
        if processed > DEFAULT_MAX_BUCHBERGER_PAIRS {
            return Err(SilenceReason::UniversalRingOutOfScope {
                detail: format!(
                    "Fp Buchberger ideal membership exceeded limit ({DEFAULT_MAX_BUCHBERGER_PAIRS})"
                ),
            });
        }
        let lm_i = &lms[i];
        let lm_j = &lms[j];
        if lm_i.gcd_is_one(lm_j) {
            continue;
        }
        let lcm = lm_i.lcm(lm_j);
        let shift_i = lcm.div_exact(lm_i).expect("lcm divisible");
        let shift_j = lcm.div_exact(lm_j).expect("lcm divisible");
        let one = basis[0].zero_coeff().one_like();
        let mut s = basis[i]
            .checked_mul_term(&shift_i, &one)
            .map_err(map_algebra_silence)?;
        s.checked_sub_mul_term_assign(&basis[j], &shift_j, &one)
            .map_err(map_algebra_silence)?;
        let red = fp_reduce(&s, &basis, order)?;
        if !red.is_zero() {
            let monic = fp_make_monic(&red, order);
            let Some((new_lm, _)) = monic.leading_term(order) else {
                continue;
            };
            let new_lm = new_lm.clone();
            let is_unit = new_lm.is_one();
            let new_idx = basis.len();
            for prev in 0..new_idx {
                pairs.push((prev, new_idx));
            }
            lms.push(new_lm);
            basis.push(monic);
            if is_unit {
                return Ok(vec![basis.pop().expect("unit pushed")]);
            }
        }
    }
    Ok(basis)
}
