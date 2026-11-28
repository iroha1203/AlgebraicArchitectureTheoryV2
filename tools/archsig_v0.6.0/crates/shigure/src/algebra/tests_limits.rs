//! AC1 リソース暴走ガード（`BigInt` bit 長上限・多項式項数上限・`ShigureLimits` 伝播）の単体テスト。

use crate::algebra::MonomialOrder;
use crate::algebra::groebner::GroebnerBasis;
use crate::algebra::linear::smith_normal_form_z_with_limits;
use crate::algebra::poly::{AlgebraError, Poly, VarOrder};
use crate::algebra::scalar::Rat;
use crate::algebra::snf::{SnfFactorizationQ, SnfFactorizationZ};
use crate::algebra::syzygy::compute_syzygies_field_with_limits;
use crate::ir::change::{ChangeSpec, EditableTarget, FixedTarget, ParamDecl};
use crate::ir::presentation::{
    ComparisonPair, CoordDecl, ObservationDecl, OperationDecl, PhaseDecl, Presentation, SortDecl,
    StateComparison, TranslatedStep, TranslatedWord, WordTranslation,
};
use crate::ir::provenance::{OriginKind, Provenance, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::ir::validate::CheckedShigureTask;
use crate::limits::{ShigureLimits, active_limits, with_active_limits};
use crate::solver::{ShigureQueryKind, execute_shigure_task};
use num_bigint::BigInt;
use std::collections::BTreeMap;

#[test]
fn groebner_enforces_bigint_bit_limit_without_false_verdict() {
    let vars = VarOrder::new(vec!["x".into(), "y".into()]).unwrap();
    let x = Poly::var(2, 0, Rat::zero());
    let y = Poly::var(2, 1, Rat::zero());
    // x - 256 (9 bit) と x^2 - y の簡約で 256^2 = 65536 (17 bit) が生成される。
    let f1 = x.sub(&Poly::constant(2, Rat::from_int(256)));
    let f2 = x.mul(&x).sub(&y);

    let limits = ShigureLimits {
        max_bigint_bits: 12,
        ..Default::default()
    };

    let err = GroebnerBasis::compute_with_limits(&[f1, f2], vars, MonomialOrder::Grevlex, &limits)
        .expect_err("17-bit coefficient must trip 12-bit limit");
    match &err {
        AlgebraError::ResourceLimitExceeded {
            limit_name,
            limit,
            observed,
            ..
        } => {
            assert_eq!(limit_name, "max_bigint_bits");
            assert_eq!(*limit, 12);
            assert!(*observed > 12);
        }
        other => panic!("expected ResourceLimitExceeded, got {other:?}"),
    }

    let silence = SilenceReason::from_algebra_with(err, |_| unreachable!("must map directly"));
    assert_eq!(silence.code(), "resource_limit_exceeded");
    let json = silence.to_json().canonical();
    assert!(json.contains("\"code\":\"resource_limit_exceeded\""));
    assert!(json.contains("\"limit_name\":\"max_bigint_bits\""));
    assert!(matches!(
        Verdict::Undetermined(silence),
        Verdict::Undetermined(..)
    ));
}

#[test]
fn groebner_and_syzygy_enforce_poly_term_limit() {
    let vars = VarOrder::new(vec!["x".into(), "y".into(), "z".into()]).unwrap();
    let x = Poly::var(3, 0, Rat::zero());
    let y = Poly::var(3, 1, Rat::zero());
    let z = Poly::var(3, 2, Rat::zero());
    let one = Poly::constant(3, Rat::from_int(1));

    // f1 = x - (y + 1)^2 (4 項), f2 = x^2 - z (2 項)
    // S 多項式 / 簡約で (y + 1)^4 - z (6 項) が現れ、上限 5 を超える。
    let y_plus_1 = y.add(&one);
    let f1 = x.sub(&y_plus_1.mul(&y_plus_1));
    let f2 = x.mul(&x).sub(&z);

    let limits = ShigureLimits {
        max_poly_terms: 5,
        ..Default::default()
    };

    let gb_err =
        GroebnerBasis::compute_with_limits(&[f1, f2], vars.clone(), MonomialOrder::Lex, &limits)
            .expect_err("expanded polynomial term count must trip max_poly_terms=5");
    assert!(matches!(
        gb_err,
        AlgebraError::ResourceLimitExceeded {
            ref limit_name,
            limit: 5,
            observed,
            ..
        } if limit_name == "max_poly_terms" && observed > 5
    ));

    // syzygy 側でも同じ項数上限を検出する。
    let syz_limits = ShigureLimits {
        max_poly_terms: 4,
        ..Default::default()
    };
    let g1 = x.sub(&y.add(&one));
    let g2 = y_plus_1.mul(&y_plus_1).sub(&z);
    let g3 = x.mul(&x).sub(&z);
    let syz_err =
        compute_syzygies_field_with_limits(&[g1, g2, g3], vars, MonomialOrder::Lex, &syz_limits)
            .expect_err("syzygy computation must enforce max_poly_terms=4");
    assert!(matches!(
        syz_err,
        AlgebraError::ResourceLimitExceeded {
            ref limit_name,
            limit: 4,
            observed,
            ..
        } if limit_name == "max_poly_terms" && observed > 4
    ));
}

#[test]
fn snf_z_and_q_enforce_bigint_bit_limit() {
    let mat_z = vec![
        vec![BigInt::from(17), BigInt::from(19)],
        vec![BigInt::from(23), BigInt::from(29)],
    ];
    let limits = ShigureLimits {
        max_bigint_bits: 5,
        ..Default::default()
    };

    let err_lin = smith_normal_form_z_with_limits(&mat_z, 2, &limits)
        .expect_err("smith_normal_form_z must trip 5-bit limit");
    assert!(matches!(
        err_lin,
        AlgebraError::ResourceLimitExceeded {
            ref limit_name,
            limit: 5,
            ..
        } if limit_name == "max_bigint_bits"
    ));

    let err_snf_z = SnfFactorizationZ::compute_with_limits(&mat_z, 2, &limits)
        .expect_err("SnfFactorizationZ must trip 5-bit limit");
    assert!(matches!(
        err_snf_z,
        AlgebraError::ResourceLimitExceeded {
            ref limit_name,
            limit: 5,
            ..
        } if limit_name == "max_bigint_bits"
    ));

    let mat_q = vec![
        vec![Rat::from_int(17), Rat::from_int(19)],
        vec![Rat::from_int(23), Rat::from_int(29)],
    ];
    let err_snf_q = SnfFactorizationQ::compute_with_limits(&mat_q, 2, &limits)
        .expect_err("SnfFactorizationQ must trip 5-bit limit");
    assert!(matches!(
        err_snf_q,
        AlgebraError::ResourceLimitExceeded {
            ref limit_name,
            limit: 5,
            ..
        } if limit_name == "max_bigint_bits"
    ));
}

#[test]
fn with_active_limits_scopes_solver_to_undetermined_resource_limit() {
    let origin = SourceRef::new("test:origin", OriginKind::HumanAdopted);
    let before = Presentation {
        name: "Before".to_owned(),
        coeff_domain: CoeffDomain::Q,
        sorts: vec![SortDecl {
            name: "D".to_owned(),
            rank: 1,
            coeff_domain: CoeffDomain::Q,
            provenance: Some(origin.clone()),
        }],
        phases: vec![PhaseDecl {
            name: "S".to_owned(),
            coords: vec![CoordDecl::symbolic("x", "D")],
            state_laws: vec![],
            provenance: Some(origin.clone()),
        }],
        operations: vec![OperationDecl {
            name: "step".to_owned(),
            source_phase: "S".to_owned(),
            target_phase: "S".to_owned(),
            args: vec![("u".to_owned(), "D".to_owned())],
            domain_laws: vec![],
            updates: BTreeMap::from([("x".to_owned(), PolyExpr::state("x") + PolyExpr::arg("u"))]),
            provenance: Some(origin.clone()),
        }],
        observations: vec![ObservationDecl {
            name: "read".to_owned(),
            phase: "S".to_owned(),
            components: vec![PolyExpr::state("x")],
            provenance: Some(origin.clone()),
        }],
        provenance: Provenance::new(vec![origin.clone()], vec![]),
    };
    let after = Presentation {
        name: "After".to_owned(),
        coeff_domain: CoeffDomain::Q,
        sorts: before.sorts.clone(),
        phases: vec![PhaseDecl {
            name: "S".to_owned(),
            coords: vec![CoordDecl::symbolic("y", "D")],
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "step".to_owned(),
            source_phase: "S".to_owned(),
            target_phase: "S".to_owned(),
            args: vec![("u".to_owned(), "D".to_owned())],
            domain_laws: vec![],
            updates: BTreeMap::from([(
                "y".to_owned(),
                PolyExpr::state("y") + PolyExpr::param("p") * PolyExpr::arg("u"),
            )]),
            provenance: Some(origin.clone()),
        }],
        observations: vec![ObservationDecl {
            name: "read".to_owned(),
            phase: "S".to_owned(),
            components: vec![PolyExpr::param("q") * PolyExpr::state("y")],
            provenance: None,
        }],
        provenance: Provenance::new(vec![origin.clone()], vec![]),
    };
    let pair = ComparisonPair {
        before,
        after,
        state_comparisons: vec![StateComparison {
            after_phase: "S".to_owned(),
            before_phase: "S".to_owned(),
            map: BTreeMap::from([("x".to_owned(), PolyExpr::param("q") * PolyExpr::state("y"))]),
            provenance: None,
        }],
        word_translation: WordTranslation {
            entries: vec![TranslatedWord {
                after_operation: "step".to_owned(),
                steps: vec![TranslatedStep {
                    before_operation: "step".to_owned(),
                    arg_exprs: vec![PolyExpr::arg("u")],
                }],
                provenance: None,
            }],
        },
    };
    let change_spec = ChangeSpec {
        name: "H".to_owned(),
        coeff_domain: CoeffDomain::Q,
        parameters: ["p", "q"]
            .into_iter()
            .map(|n| ParamDecl {
                name: n.to_owned(),
                coeff_domain: CoeffDomain::Q,
                provenance: None,
            })
            .collect(),
        fixed: vec![FixedTarget::ObservationExpr {
            presentation: "Before".to_owned(),
            phase: "S".to_owned(),
            observation: "read".to_owned(),
        }],
        editable: vec![
            EditableTarget::OperationExpr {
                presentation: "After".to_owned(),
                operation: "step".to_owned(),
            },
            EditableTarget::StateComparisonExpr {
                after_phase: "S".to_owned(),
            },
        ],
        provenance: Provenance::new(vec![origin], vec![]),
    };
    let task = CheckedShigureTask::validate(pair, change_spec, None).unwrap();

    let before_limits = active_limits();
    let strict = ShigureLimits {
        max_poly_terms: 1,
        ..Default::default()
    };
    let outcome = with_active_limits(&strict, || {
        execute_shigure_task(&task, ShigureQueryKind::ConditionalSolutionSpace)
    });
    assert_eq!(active_limits(), before_limits);
    match outcome.verdict {
        Verdict::Undetermined(SilenceReason::ResourceLimitExceeded {
            limit_name, limit, ..
        }) => {
            assert_eq!(limit_name, "max_poly_terms");
            assert_eq!(limit, 1);
        }
        other => panic!("expected ResourceLimitExceeded, got {other:?}"),
    }
}

#[test]
fn poly_expr_expand_substitute_q_linear_and_z_syzygy_enforce_limits() {
    use crate::algebra::artin::rref_field;
    use crate::algebra::constructible::map_constructible_silence;
    use crate::algebra::linear::solve_affine_q;
    use crate::algebra::poly_expr::ExprBindings;
    use crate::algebra::syzygy::compute_syzygies_z_with_limits;

    let (_, bindings) = ExprBindings::from_slices(&["x".into(), "y".into()], &[], &[]).unwrap();
    let strict_terms = ShigureLimits {
        max_poly_terms: 4,
        ..Default::default()
    };
    let expr = PolyExpr::Pow(
        Box::new(PolyExpr::state("x") + PolyExpr::state("y") + PolyExpr::int(1)),
        3,
    );
    let expand_err = with_active_limits(&strict_terms, || Poly::from_expr_q(&expr, &bindings))
        .expect_err("PolyExpr expansion must enforce max_poly_terms");
    assert!(matches!(
        expand_err,
        AlgebraError::ResourceLimitExceeded {
            ref limit_name,
            limit: 4,
            ..
        } if limit_name == "max_poly_terms"
    ));

    // map_constructible_silence preserves ResourceLimitExceeded instead of squashing
    let preserved = map_constructible_silence(expand_err);
    assert_eq!(preserved.code(), "resource_limit_exceeded");

    // Poly::substitute enforces active max_poly_terms
    let vars = VarOrder::new(vec!["x".into(), "y".into()]).unwrap();
    let x = Poly::var(2, 0, Rat::zero());
    let y = Poly::var(2, 1, Rat::zero());
    let one = Poly::constant(2, Rat::from_int(1));
    let x_cubed = x.mul(&x).mul(&x);
    let sub_err = with_active_limits(&strict_terms, || {
        x_cubed.substitute(&[x.add(&y).add(&one), y.clone()])
    })
    .expect_err("Poly::substitute must enforce max_poly_terms");
    assert!(matches!(
        sub_err,
        AlgebraError::ResourceLimitExceeded {
            ref limit_name,
            limit: 4,
            ..
        } if limit_name == "max_poly_terms"
    ));

    // rref_field & solve_affine_q enforce active max_bigint_bits
    let strict_bits = ShigureLimits {
        max_bigint_bits: 5,
        ..Default::default()
    };
    let mat_q = vec![
        vec![Rat::from_int(17), Rat::from_int(19)],
        vec![Rat::from_int(23), Rat::from_int(29)],
    ];
    let rhs_q = vec![Rat::from_int(1), Rat::from_int(2)];
    let rref_err = with_active_limits(&strict_bits, || rref_field(&mat_q, 2, &Rat::zero()))
        .expect_err("rref_field must enforce max_bigint_bits");
    assert!(matches!(
        rref_err,
        AlgebraError::ResourceLimitExceeded {
            ref limit_name,
            limit: 5,
            ..
        } if limit_name == "max_bigint_bits"
    ));
    let q_err = with_active_limits(&strict_bits, || solve_affine_q(&mat_q, &rhs_q, 2))
        .expect_err("solve_affine_q must enforce max_bigint_bits");
    assert!(matches!(
        q_err,
        AlgebraError::ResourceLimitExceeded {
            ref limit_name,
            limit: 5,
            ..
        } if limit_name == "max_bigint_bits"
    ));

    // compute_syzygies_z_with_limits monomial Case 1 enforces max_bigint_bits
    let mono_1 = Poly::constant(2, BigInt::from(7)).mul(&Poly::var(2, 0, BigInt::from(0)));
    let mono_2 = Poly::constant(2, BigInt::from(11)).mul(&Poly::var(2, 1, BigInt::from(0)));
    let syz_z_err = compute_syzygies_z_with_limits(&[mono_1, mono_2], vars, &strict_bits)
        .expect_err("Z monomial syzygy lcm=77 (7 bits) must exceed max_bigint_bits=5");
    assert!(matches!(
        syz_z_err,
        AlgebraError::ResourceLimitExceeded {
            ref limit_name,
            limit: 5,
            ..
        } if limit_name == "max_bigint_bits"
    ));
}

#[test]
fn post_elim_q_affine_and_z_existential_preserve_resource_limit_exceeded() {
    use crate::algebra::linear::{SystemPointOutcome, solve_polynomial_system_q};
    use crate::ir::change::PointDomain;
    use crate::ir::family::{
        CandidateFamilySpec, CandidateMember, CandidateSpace, FamilySpec, GoodnessSpec,
        PreservationGoodnessSource, RealizationFamilySpec, RealizationMember, RealizationSpace,
    };
    use crate::ir::presentation::CoordValue;
    use crate::ir::provenance::SourceRef;
    use crate::ir::robustness::{CandidateSelector, CheckedRobustnessTask, RobustnessTaskSpec};
    use crate::ir::term::ScalarLit;
    use crate::solver::solve_robustness_task;

    // 1. solve_polynomial_system_q (RationalPoints): rabinowitsch_solve passes <= 8 bits,
    //    then post-elimination solve_affine_q exceeds max_bigint_bits=8.
    let vars = VarOrder::new(vec!["w".into(), "y".into(), "x".into(), "z".into()]).unwrap();
    let w = Poly::var(4, 0, Rat::zero());
    let y = Poly::var(4, 1, Rat::zero());
    let x = Poly::var(4, 2, Rat::zero());
    let z = Poly::var(4, 3, Rat::zero());
    let eqs = vec![
        w.mul(&w),
        w,
        Poly::constant(4, Rat::from_int(31))
            .mul(&y)
            .add(&Poly::constant(4, Rat::from_int(37)).mul(&x))
            .sub(&Poly::constant(4, Rat::from_int(1))),
        Poly::constant(4, Rat::from_int(41))
            .mul(&x)
            .add(&Poly::constant(4, Rat::from_int(43)).mul(&z))
            .sub(&Poly::constant(4, Rat::from_int(2))),
    ];
    let limit_8 = ShigureLimits {
        max_bigint_bits: 8,
        ..Default::default()
    };
    let q_outcome = with_active_limits(&limit_8, || {
        solve_polynomial_system_q(&eqs, &[], &vars, &PointDomain::RationalPoints)
    });
    assert!(
        matches!(
            q_outcome,
            SystemPointOutcome::Undetermined(SilenceReason::ResourceLimitExceeded {
                ref limit_name,
                limit: 8,
                ..
            }) if limit_name == "max_bigint_bits"
        ),
        "expected ResourceLimitExceeded, got {q_outcome:?}"
    );

    // 2. Z + IntegerPoints existential robustness must return Undetermined(ResourceLimitExceeded),
    //    never Refuted via fail_pair when inner solver hits max_bigint_bits.
    let z_origin = SourceRef::new("test:z", OriginKind::HumanAdopted);
    let make_z_pres = |name: &str, step_delta: PolyExpr| Presentation {
        name: name.to_owned(),
        coeff_domain: CoeffDomain::Z,
        sorts: vec![SortDecl {
            name: "S".to_owned(),
            rank: 1,
            coeff_domain: CoeffDomain::Z,
            provenance: Some(z_origin.clone()),
        }],
        phases: vec![PhaseDecl {
            name: "Active".to_owned(),
            coords: vec![CoordDecl::symbolic("x", "S")],
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "step".to_owned(),
            source_phase: "Active".to_owned(),
            target_phase: "Active".to_owned(),
            args: vec![],
            domain_laws: vec![],
            updates: BTreeMap::from([("x".to_owned(), PolyExpr::state("x") + step_delta)]),
            provenance: None,
        }],
        observations: vec![ObservationDecl {
            name: "obs".to_owned(),
            phase: "Active".to_owned(),
            components: vec![PolyExpr::state("x")],
            provenance: None,
        }],
        provenance: Provenance::default(),
    };
    let z_fam = FamilySpec {
        name: "ZExist".to_owned(),
        coeff_domain: CoeffDomain::Z,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["u".to_owned()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::FiniteMembers(vec![RealizationMember {
                id: "u1".to_owned(),
                assignments: BTreeMap::from([(
                    "u".to_owned(),
                    CoordValue::Observed(ScalarLit::Z(BigInt::from(1))),
                )]),
                is_raw_candidate: false,
                presentation: None,
                origin: z_origin.clone(),
            }]),
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec!["c".to_owned()],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c1".to_owned(),
                assignments: BTreeMap::from([(
                    "c".to_owned(),
                    CoordValue::Observed(ScalarLit::Z(BigInt::from(1))),
                )]),
                origin: z_origin.clone(),
            }]),
        },
        goodness: GoodnessSpec::Existential {
            witness_vars: vec!["w".to_owned()],
            equations: vec![],
            invertibles: vec![],
            preservation: Some(PreservationGoodnessSource {
                pair: ComparisonPair {
                    before: make_z_pres("BeforeZ", PolyExpr::Const(ScalarLit::Z(BigInt::from(20)))),
                    after: make_z_pres("AfterZ", PolyExpr::param("p")),
                    state_comparisons: vec![StateComparison {
                        after_phase: "Active".to_owned(),
                        before_phase: "Active".to_owned(),
                        map: BTreeMap::from([("x".to_owned(), PolyExpr::state("x"))]),
                        provenance: None,
                    }],
                    word_translation: WordTranslation {
                        entries: vec![TranslatedWord {
                            after_operation: "step".to_owned(),
                            steps: vec![TranslatedStep {
                                before_operation: "step".to_owned(),
                                arg_exprs: vec![],
                            }],
                            provenance: None,
                        }],
                    },
                },
                change_spec: ChangeSpec {
                    name: "HZ".to_owned(),
                    coeff_domain: CoeffDomain::Z,
                    parameters: vec![ParamDecl {
                        name: "p".to_owned(),
                        coeff_domain: CoeffDomain::Z,
                        provenance: None,
                    }],
                    fixed: vec![],
                    editable: vec![EditableTarget::OperationExpr {
                        presentation: "AfterZ".to_owned(),
                        operation: "step".to_owned(),
                    }],
                    provenance: Provenance::default(),
                },
                param_bindings: BTreeMap::from([("p".to_owned(), PolyExpr::param("w"))]),
            }),
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };
    let r_task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "z_exist_limit".to_owned(),
        family: z_fam,
        point_domain: PointDomain::IntegerPoints,
        base_value: vec![],
        designated_candidate: Some(CandidateSelector::ById("c1".to_owned())),
        check_universal_ring: false,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    let limit_3 = ShigureLimits {
        max_bigint_bits: 3,
        ..Default::default()
    };
    let r_out = with_active_limits(&limit_3, || solve_robustness_task(&r_task));
    assert!(
        matches!(
            r_out.verdict,
            Verdict::Undetermined(SilenceReason::ResourceLimitExceeded {
                ref limit_name,
                limit: 3,
                ..
            }) if limit_name == "max_bigint_bits"
        ),
        "expected Undetermined(ResourceLimitExceeded), got {:?}",
        r_out.verdict
    );
}
