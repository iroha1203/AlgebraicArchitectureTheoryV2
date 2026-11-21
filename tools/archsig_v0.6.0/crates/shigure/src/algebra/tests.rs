use super::*;
use crate::ir::change::PointDomain;
use crate::ir::result::SilenceReason;
use crate::ir::term::PolyExpr;
use num_bigint::{BigInt, BigUint};
use num_traits::Signed;
use std::collections::BTreeMap;

fn rat(n: i64, d: i64) -> Rat {
    Rat::new(n, d).expect("nonzero denominator")
}

fn poly_q(expr: &PolyExpr, vars: &VarOrder) -> Poly<Rat> {
    Poly::from_expr_q(expr, vars).expect("valid Q polynomial expression")
}

fn q_lit(n: i64) -> PolyExpr {
    PolyExpr::rat(n, 1).expect("valid integer rational")
}

#[test]
fn scalar_field_axioms_and_prime_checks_hold_parametrically() {
    assert!(Rat::new(1, 0).is_none());
    assert!(FpElem::new(BigInt::from(1), BigUint::from(9u32)).is_none());

    for &p in &[2u32, 3, 5, 7, 11, 101] {
        let m = BigUint::from(p);
        for a in 1..p.min(7) {
            let elem = FpElem::new(BigInt::from(a), m.clone()).unwrap();
            let inv = elem.inv().expect("nonzero element in F_p has inverse");
            assert!(elem.mul_checked(&inv).unwrap().is_one());
            let neg = elem.neg_elem();
            assert!(elem.add_checked(&neg).unwrap().is_zero());
        }
        assert!(FpElem::zero(m.clone()).unwrap().inv().is_none());
    }

    let pairs = [(3, 4), (-5, 6), (7, 1), (0, 1), (-2, 9)];
    for (n1, d1) in pairs {
        let a = rat(n1, d1);
        for (n2, d2) in pairs {
            let b = rat(n2, d2);
            assert_eq!(&a + &b, &b + &a);
            assert_eq!(&a * &b, &b * &a);
            if !a.is_zero() {
                assert!((&a * &a.inv().unwrap()).is_one());
            }
        }
    }
}

#[test]
fn unobserved_poly_expr_is_never_coerced_to_zero() {
    let vars = VarOrder::new(vec!["x".into()]).unwrap();
    let expr = PolyExpr::param("x") + PolyExpr::unobserved("Ledger.Idle.missing_x", None);
    let err = Poly::from_expr_q(&expr, &vars).unwrap_err();
    assert_eq!(
        err,
        AlgebraError::UnobservedDependency {
            slots: vec!["Ledger.Idle.missing_x".to_owned()],
        }
    );
}

#[test]
fn groebner_basis_membership_and_witness_verification() {
    let vars = VarOrder::new(vec!["x".into(), "y".into(), "z".into()]).unwrap();
    let x = PolyExpr::param("x");
    let y = PolyExpr::param("y");
    let z = PolyExpr::param("z");

    let f0 = poly_q(&(PolyExpr::pow(x.clone(), 2) - y.clone()), &vars);
    let f1 = poly_q(&(PolyExpr::pow(x.clone(), 3) - z.clone()), &vars);
    let gb = GroebnerBasis::compute(
        &[f0.clone(), f1.clone()],
        vars.clone(),
        MonomialOrder::Grevlex,
    )
    .expect("Groebner basis converges");

    // `y^3 - z^2 = -(y^2 + x^2*y + x^4)*(x^2 - y) + (x^3 + z)*(x^3 - z)` belongs to `(x^2 - y, x^3 - z)`.
    let member = poly_q(
        &(PolyExpr::pow(y.clone(), 3) - PolyExpr::pow(z.clone(), 2)),
        &vars,
    );
    let res = gb.membership(&member).unwrap();
    assert!(res.is_member);
    assert!(res.verified);
    assert!(res.remainder.is_zero());
    // Independent check of witness sum_i h_i * f_i == member.
    let reconstructed = res.cofactors[0].mul(&f0).add(&res.cofactors[1].mul(&f1));
    assert_eq!(reconstructed, member);

    // `y - z` is NOT in `(x^2 - y, x^3 - z)` (at x=2, y=4, z=8 => y-z = -4 != 0).
    let non_member = poly_q(&(y - z), &vars);
    let non_res = gb.membership(&non_member).unwrap();
    assert!(!non_res.is_member);
    assert!(non_res.verified);
    assert!(!non_res.remainder.is_zero());

    // Parametric inconsistent ideals `(x^2 - k, x^2 - (k + 1))` produce verified `1 = sum h_i f_i`.
    for k in [1i64, 2, 3, 5] {
        let g0 = poly_q(&(PolyExpr::pow(x.clone(), 2) - q_lit(k)), &vars);
        let g1 = poly_q(&(PolyExpr::pow(x.clone(), 2) - q_lit(k + 1)), &vars);
        let inc_gb = GroebnerBasis::compute(
            &[g0.clone(), g1.clone()],
            vars.clone(),
            MonomialOrder::Grevlex,
        )
        .unwrap();
        assert!(inc_gb.contains_one());
        let witness = inc_gb
            .empty_witness()
            .unwrap()
            .expect("empty witness exists");
        assert!(witness.verified);
        let one = Poly::one(vars.len(), Rat::zero());
        let mem = inc_gb.membership(&one).unwrap();
        assert!(mem.is_member && mem.verified);
        assert_eq!(
            mem.cofactors[0].mul(&g0).add(&mem.cofactors[1].mul(&g1)),
            one
        );
    }
}

#[test]
fn rabinowitsch_ledger_conditions_match_g140_p6() {
    let vars2 = VarOrder::new(vec!["delta".into(), "mu".into()]).unwrap();
    let delta = PolyExpr::param("delta");
    let mu = PolyExpr::param("mu");
    let mu_delta = poly_q(&(mu.clone() * delta.clone()), &vars2);
    let p_delta = poly_q(&delta, &vars2);
    let p_mu = poly_q(&mu, &vars2);

    // V(mu*delta) ∩ D(mu) forces delta = 0.
    let res_d_mu = rabinowitsch_solve(
        std::slice::from_ref(&mu_delta),
        std::slice::from_ref(&p_mu),
        &vars2,
    )
    .unwrap();
    assert!(!res_d_mu.is_empty_over_closure);
    assert_eq!(res_d_mu.parameter_equations, vec![p_delta.clone()]);

    // V(mu*delta) ∩ D(delta) forces mu = 0.
    let res_d_delta = rabinowitsch_solve(
        std::slice::from_ref(&mu_delta),
        std::slice::from_ref(&p_delta),
        &vars2,
    )
    .unwrap();
    assert!(!res_d_delta.is_empty_over_closure);
    assert_eq!(res_d_delta.parameter_equations, vec![p_mu.clone()]);

    // V(mu*delta) ∩ D(mu*delta) is empty with verified witness 1 = sum h_i f_i.
    let res_empty = rabinowitsch_solve(
        std::slice::from_ref(&mu_delta),
        std::slice::from_ref(&mu_delta),
        &vars2,
    )
    .unwrap();
    assert!(res_empty.is_empty_over_closure);
    let witness = res_empty.empty_witness.expect("empty witness required");
    assert!(witness.verified);

    // V(mu*delta*(1 - rho)) ∩ D(mu*delta) forces rho - 1 = 0.
    let vars3 = VarOrder::new(vec!["delta".into(), "mu".into(), "rho".into()]).unwrap();
    let rho = PolyExpr::param("rho");
    let residual3 = poly_q(
        &(mu.clone() * delta.clone() * (q_lit(1) - rho.clone())),
        &vars3,
    );
    let inv3 = poly_q(&(mu * delta), &vars3);
    let res3 = rabinowitsch_solve(&[residual3], &[inv3], &vars3).unwrap();
    assert!(!res3.is_empty_over_closure);
    let expected_rho = poly_q(&(rho - q_lit(1)), &vars3);
    assert_eq!(res3.parameter_equations, vec![expected_rho]);
}

#[test]
fn quotient_ring_membership_does_not_strengthen_to_ambient_zero() {
    // AC5(a) canonical example: R[y]/(a*y) with target y = 0 holds precisely on D(a).
    let combined = VarOrder::new(vec!["y".into(), "a".into()]).unwrap();
    let param_vars = VarOrder::new(vec!["a".into()]).unwrap();
    let y = poly_q(&PolyExpr::state("y"), &combined);
    let ay = poly_q(&(PolyExpr::param("a") * PolyExpr::state("y")), &combined);
    let strata = quotient_membership_locus(&y, &[ay], 1, &param_vars)
        .expect("quotient stratification succeeds");
    let a_param = poly_q(&PolyExpr::param("a"), &param_vars);
    assert_eq!(strata.len(), 1);
    assert!(strata[0].equations.is_empty());
    assert_eq!(strata[0].invertibles, vec![a_param]);

    // G-140 P3 Busy Law: g = mu*(h - C), target apply_u^*(g) = mu*(h - C) - mu*delta*u.
    let busy_vars = VarOrder::new(vec![
        "h".into(),
        "C".into(),
        "u".into(),
        "delta".into(),
        "mu".into(),
    ])
    .unwrap();
    let busy_params = VarOrder::new(vec!["delta".into(), "mu".into()]).unwrap();
    let g_expr = PolyExpr::param("mu") * (PolyExpr::state("h") - PolyExpr::state("C"));
    let apply_g_expr =
        g_expr.clone() - PolyExpr::param("mu") * PolyExpr::param("delta") * PolyExpr::arg("u");
    let g_poly = poly_q(&g_expr, &busy_vars);
    let apply_g_poly = poly_q(&apply_g_expr, &busy_vars);

    let busy_strata = quotient_membership_locus(
        &apply_g_poly,
        std::slice::from_ref(&g_poly),
        3,
        &busy_params,
    )
    .expect("Busy Law quotient stratification succeeds");
    // Exact decomposition of V(mu*delta): V(mu) ∪ (V(delta) ∩ D(mu)).
    let p_delta = poly_q(&PolyExpr::param("delta"), &busy_params);
    let p_mu = poly_q(&PolyExpr::param("mu"), &busy_params);
    assert_eq!(busy_strata.len(), 2);
    assert!(
        busy_strata
            .iter()
            .any(|s| s.equations == vec![p_mu.clone()] && s.invertibles.is_empty())
    );
    assert!(
        busy_strata
            .iter()
            .any(|s| s.equations == vec![p_delta.clone()] && s.invertibles == vec![p_mu.clone()])
    );

    // G-140 P3 finish read diff = g = mu*(h - C) in (g): holds on V(mu) ∪ D(mu) = all points,
    // NEVER forcing ambient mu = 0!
    let finish_strata =
        quotient_membership_locus(&g_poly, std::slice::from_ref(&g_poly), 3, &busy_params)
            .expect("finish read diff quotient stratification succeeds");
    assert!(
        finish_strata
            .iter()
            .any(|s| s.equations.is_empty() && s.invertibles == vec![p_mu.clone()])
    );
}

#[test]
fn affine_q_and_smith_z_and_fp_enumeration_are_exact_and_verified() {
    // Q affine consistent with 1-dim kernel: x + y = 3, 2x + 2y = 6.
    let mat_q = vec![vec![rat(1, 1), rat(1, 1)], vec![rat(2, 1), rat(2, 1)]];
    let rhs_q = vec![rat(3, 1), rat(6, 1)];
    match solve_affine_q(&mat_q, &rhs_q, 2).unwrap() {
        AffineSolutionQ::Consistent {
            particular,
            kernel_basis,
            verified,
        } => {
            assert!(verified);
            assert_eq!(kernel_basis.len(), 1);
            assert_eq!(&particular[0] + &particular[1], rat(3, 1));
        }
        other => panic!("expected consistent Q affine solution, got {other:?}"),
    }

    // Q affine inconsistent: x + y = 1, x + y = 2.
    let inc_q = solve_affine_q(
        &[vec![rat(1, 1), rat(1, 1)], vec![rat(1, 1), rat(1, 1)]],
        &[rat(1, 1), rat(2, 1)],
        2,
    )
    .unwrap();
    assert!(matches!(
        inc_q,
        AffineSolutionQ::Inconsistent { verified: true, .. }
    ));

    // Z affine Smith normal form: 2x + 4y = 6 (consistent) vs 2x + 4y = 5 (inconsistent over Z).
    let mat_z = vec![vec![BigInt::from(2), BigInt::from(4)]];
    match solve_affine_z(&mat_z, &[BigInt::from(6)], 2).unwrap() {
        AffineSolutionZ::Consistent {
            particular,
            kernel_basis,
            smith_diagonals,
            verified,
        } => {
            assert!(verified);
            assert_eq!(smith_diagonals, vec![BigInt::from(2)]);
            assert_eq!(kernel_basis.len(), 1);
            assert_eq!(
                BigInt::from(2) * &particular[0] + BigInt::from(4) * &particular[1],
                BigInt::from(6)
            );
        }
        other => panic!("expected consistent Z affine solution, got {other:?}"),
    }

    match solve_affine_z(&mat_z, &[BigInt::from(5)], 2).unwrap() {
        AffineSolutionZ::Inconsistent {
            divisor,
            rhs_value,
            verified,
            ..
        } => {
            assert!(verified);
            assert_eq!(divisor, Some(BigInt::from(2)));
            assert_eq!(rhs_value.abs(), BigInt::from(5));
        }
        other => panic!("expected inconsistent Z affine solution, got {other:?}"),
    }

    // F_3 full enumeration for mu*delta*(1 - rho) = 0 with D(mu*delta):
    // exactly (3 - 1)^2 = 4 solutions, all forcing rho = 1.
    let p3 = BigUint::from(3u32);
    let vars3 = VarOrder::new(vec!["delta".into(), "mu".into(), "rho".into()]).unwrap();
    let one_fp =
        PolyExpr::Const(crate::ir::term::ScalarLit::fp(BigInt::from(1), p3.clone()).unwrap());
    let eq_fp = Poly::from_expr_fp(
        &(PolyExpr::param("mu") * PolyExpr::param("delta") * (one_fp - PolyExpr::param("rho"))),
        &vars3,
        &p3,
    )
    .unwrap();
    let inv_fp = Poly::from_expr_fp(
        &(PolyExpr::param("mu") * PolyExpr::param("delta")),
        &vars3,
        &p3,
    )
    .unwrap();
    let fp_res = solve_fp_enumeration(&[eq_fp], &[inv_fp], 3, &p3, DEFAULT_MAX_FP_POINTS).unwrap();
    assert_eq!(fp_res.total_domain_size, 27);
    assert_eq!(fp_res.solutions.len(), 4);
    for sol in &fp_res.solutions {
        assert!(!sol[0].is_zero());
        assert!(!sol[1].is_zero());
        assert!(sol[2].is_one());
    }

    // Exceeding enumeration bound fails closed with SilenceReason (never partial enumeration).
    let err = solve_fp_enumeration(&[], &[], 4, &p3, 10).unwrap_err();
    assert!(matches!(
        err,
        SilenceReason::ApplicabilityConditionNotMet { .. }
    ));
}

#[test]
fn silence_discipline_distinguishes_algebraic_closure_from_q_and_z_points() {
    let vars = VarOrder::new(vec!["x".into()]).unwrap();
    let x = PolyExpr::param("x");
    let x2_plus_1 = poly_q(&(PolyExpr::pow(x.clone(), 2) + q_lit(1)), &vars);
    let x2_plus_2 = poly_q(&(PolyExpr::pow(x.clone(), 2) + q_lit(2)), &vars);

    // x^2 + 1 = 0: nonempty over algebraic closure, Undetermined over Q_points and Z_points.
    assert!(matches!(
        solve_polynomial_system_q(
            std::slice::from_ref(&x2_plus_1),
            &[],
            &vars,
            &PointDomain::AlgebraicClosure
        ),
        SystemPointOutcome::NonEmptyOverClosure { .. }
    ));
    assert!(matches!(
        solve_polynomial_system_q(
            std::slice::from_ref(&x2_plus_1),
            &[],
            &vars,
            &PointDomain::RationalPoints
        ),
        SystemPointOutcome::Undetermined(SilenceReason::NonLinearRationalOrIntegerExistence {
            point_domain: PointDomain::RationalPoints,
            ..
        })
    ));
    assert!(matches!(
        solve_polynomial_system_q(
            std::slice::from_ref(&x2_plus_1),
            &[],
            &vars,
            &PointDomain::IntegerPoints
        ),
        SystemPointOutcome::Undetermined(SilenceReason::NonLinearRationalOrIntegerExistence {
            point_domain: PointDomain::IntegerPoints,
            ..
        })
    ));

    // x^2 + 1 = 0, x^2 + 2 = 0: empty even over algebraic closure => Empty with witness over Q/Z too.
    assert!(matches!(
        solve_polynomial_system_q(
            &[x2_plus_1.clone(), x2_plus_2.clone()],
            &[],
            &vars,
            &PointDomain::RationalPoints,
        ),
        SystemPointOutcome::Empty {
            witness: Some(ref w),
        } if w.verified
    ));
    assert!(matches!(
        solve_polynomial_system_q(
            &[x2_plus_1, x2_plus_2],
            &[],
            &vars,
            &PointDomain::IntegerPoints,
        ),
        SystemPointOutcome::Empty {
            witness: Some(ref w),
        } if w.verified
    ));

    // Affine 2x - 3 = 0: consistent over Q (x = 3/2), inconsistent over Z.
    let affine_eq = poly_q(&(q_lit(2) * x - q_lit(3)), &vars);
    assert!(matches!(
        solve_polynomial_system_q(
            std::slice::from_ref(&affine_eq),
            &[],
            &vars,
            &PointDomain::RationalPoints
        ),
        SystemPointOutcome::AffineQ(AffineSolutionQ::Consistent { verified: true, .. })
    ));
    assert!(matches!(
        solve_polynomial_system_q(&[affine_eq], &[], &vars, &PointDomain::IntegerPoints),
        SystemPointOutcome::AffineZ(AffineSolutionZ::Inconsistent { verified: true, .. })
    ));
}

#[test]
fn coordinate_plane_interaction_matches_ac4_and_g141_f10_f12() {
    // 1. Ledger mu*delta: 2-variable interaction, minimal failing subset {delta, mu}, r = 1.
    let vars2 = VarOrder::new(vec!["delta".into(), "mu".into()]).unwrap();
    let mu_delta = poly_q(&(PolyExpr::param("mu") * PolyExpr::param("delta")), &vars2);
    let summary2 = analyze_coordinate_interaction(&[mu_delta], &vars2).unwrap();
    assert_eq!(summary2.min_interacting_variables, Some(2));
    assert_eq!(summary2.max_vanishing_subset_size, Some(1));
    assert_eq!(
        summary2.minimal_failing_subsets,
        vec![vec!["delta".to_owned(), "mu".to_owned()]]
    );

    // 2. Single-variable higher power t^m (m = 1, 2, 3, 5): always 1-variable interaction, r = 0.
    let vars1 = VarOrder::new(vec!["t".into()]).unwrap();
    for m in [1u32, 2, 3, 5] {
        let tm = poly_q(&PolyExpr::pow(PolyExpr::param("t"), m), &vars1);
        let s = analyze_coordinate_interaction(&[tm], &vars1).unwrap();
        assert_eq!(s.min_interacting_variables, Some(1));
        assert_eq!(s.max_vanishing_subset_size, Some(0));
        assert_eq!(s.minimal_failing_subsets, vec![vec!["t".to_owned()]]);
    }

    // 3. 3-variable mu*delta*(1 - rho): rho = 0 face fails on {delta, mu}; rho = 1 resolves completely.
    let vars3 = VarOrder::new(vec!["delta".into(), "mu".into(), "rho".into()]).unwrap();
    let poly3 = poly_q(
        &(PolyExpr::param("mu") * PolyExpr::param("delta") * (q_lit(1) - PolyExpr::param("rho"))),
        &vars3,
    );
    let full3 = analyze_coordinate_interaction(std::slice::from_ref(&poly3), &vars3).unwrap();
    assert_eq!(full3.min_interacting_variables, Some(2));
    assert_eq!(full3.max_vanishing_subset_size, Some(1));
    assert_eq!(
        full3.minimal_failing_subsets,
        vec![vec!["delta".to_owned(), "mu".to_owned()]]
    );

    let face_rho0 = analyze_interaction_on_face(
        std::slice::from_ref(&poly3),
        &vars3,
        &BTreeMap::from([("rho".to_owned(), rat(0, 1))]),
    )
    .unwrap();
    assert_eq!(face_rho0.min_interacting_variables, Some(2));
    assert_eq!(
        face_rho0.minimal_failing_subsets,
        vec![vec!["delta".to_owned(), "mu".to_owned()]]
    );

    let face_rho1 = analyze_interaction_on_face(
        &[poly3],
        &vars3,
        &BTreeMap::from([("rho".to_owned(), rat(1, 1))]),
    )
    .unwrap();
    assert_eq!(face_rho1.min_interacting_variables, None);
    assert_eq!(face_rho1.max_vanishing_subset_size, Some(2));
    assert!(face_rho1.minimal_failing_subsets.is_empty());

    // 4. Constant residual vs zero ideal vs open-condition silence guard.
    let const_one = Poly::one(vars2.len(), Rat::zero());
    let const_sum = analyze_coordinate_interaction(&[const_one], &vars2).unwrap();
    assert_eq!(const_sum.min_interacting_variables, Some(0));
    assert_eq!(const_sum.max_vanishing_subset_size, None);
    assert_eq!(
        const_sum.minimal_failing_subsets,
        vec![Vec::<String>::new()]
    );

    assert!(matches!(
        require_closed_for_interaction(true),
        Err(SilenceReason::OpenConditionInInteraction { .. })
    ));
    assert!(require_closed_for_interaction(false).is_ok());
}

#[test]
fn edge_cases_empty_constant_ideals_multigen_quotient_and_negative_smith() {
    let vars = VarOrder::new(vec!["x".into()]).unwrap();
    let empty_gb = GroebnerBasis::compute(&[], vars.clone(), MonomialOrder::Grevlex).unwrap();
    assert!(!empty_gb.contains_one());
    assert!(
        empty_gb
            .membership(&Poly::zero(1, Rat::zero()))
            .unwrap()
            .is_member
    );
    assert!(
        !empty_gb
            .membership(&Poly::one(1, Rat::zero()))
            .unwrap()
            .is_member
    );

    let const_gb = GroebnerBasis::compute(
        &[Poly::constant(1, rat(3, 1)), Poly::var(1, 0, Rat::zero())],
        vars,
        MonomialOrder::Grevlex,
    )
    .unwrap();
    assert!(const_gb.contains_one());
    assert!(const_gb.empty_witness().unwrap().expect("witness").verified);

    // Multi-generator quotient ideal: J = (a*y - z, b*z) in Q[a, b][y, z], target = y.
    // y in (a*y - z, b*z) holds iff both a and b are invertible (y = a^-1*(a*y - z) + (a*b)^-1*(b*z)).
    let comb = VarOrder::new(vec!["y".into(), "z".into(), "a".into(), "b".into()]).unwrap();
    let pvars = VarOrder::new(vec!["a".into(), "b".into()]).unwrap();
    let g1 = poly_q(
        &(PolyExpr::param("a") * PolyExpr::state("y") - PolyExpr::state("z")),
        &comb,
    );
    let g2 = poly_q(&(PolyExpr::param("b") * PolyExpr::state("z")), &comb);
    let target_y = poly_q(&PolyExpr::state("y"), &comb);
    let strata = quotient_membership_locus(&target_y, &[g1, g2], 2, &pvars).unwrap();
    let pa = poly_q(&PolyExpr::param("a"), &pvars);
    let pb = poly_q(&PolyExpr::param("b"), &pvars);
    assert_eq!(strata.len(), 1);
    assert!(strata[0].equations.is_empty());
    assert!(strata[0].invertibles.contains(&pa));
    assert!(strata[0].invertibles.contains(&pb));

    // Negative / non-diagonal Smith normal form: [[-6, 9], [4, -6]] * x = [3, -2] (consistent)
    // and [[-6, 9], [4, -6]] * x = [3, 0] (inconsistent over Z).
    let mat = vec![
        vec![BigInt::from(-6), BigInt::from(9)],
        vec![BigInt::from(4), BigInt::from(-6)],
    ];
    match solve_affine_z(&mat, &[BigInt::from(3), BigInt::from(-2)], 2).unwrap() {
        AffineSolutionZ::Consistent {
            smith_diagonals,
            kernel_basis,
            verified,
            ..
        } => {
            assert!(verified);
            assert_eq!(smith_diagonals, vec![BigInt::from(1)]);
            assert_eq!(kernel_basis.len(), 1);
        }
        other => panic!("expected consistent Z affine solution, got {other:?}"),
    }
    assert!(matches!(
        solve_affine_z(&mat, &[BigInt::from(3), BigInt::from(0)], 2).unwrap(),
        AffineSolutionZ::Inconsistent { verified: true, .. }
    ));
}
