//! Step 2 `solver/lift` Round 3 / Round 4 監査回帰テスト。

use crate::ir::change::NamedPoly;
use crate::ir::lift::{
    DeclarationContextSpec, DeclarationCoverSpec, LiftTaskSpec, RawReadComparisonSpec,
    RelativeReadingSpec, RingParamSpec, SquareZeroSpec, TwoContextCechSpec, validate_lift_task,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::Verdict;
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::solver::solve_lift_task;
use num_bigint::BigInt;

fn prov(clauses: Vec<MathClause>) -> Provenance {
    Provenance::new(
        vec![SourceRef::new("test:lift_r3_r4", OriginKind::HumanAdopted)],
        clauses,
    )
}

fn sv(name: &str) -> PolyExpr {
    PolyExpr::StateVar(name.into())
}

fn cz(n: i64) -> PolyExpr {
    PolyExpr::Const(ScalarLit::Z(BigInt::from(n)))
}

fn sub(a: PolyExpr, b: PolyExpr) -> PolyExpr {
    PolyExpr::Sub(Box::new(a), Box::new(b))
}

fn mul(a: PolyExpr, b: PolyExpr) -> PolyExpr {
    PolyExpr::Mul(Box::new(a), Box::new(b))
}

fn pow(a: PolyExpr, e: u32) -> PolyExpr {
    PolyExpr::Pow(Box::new(a), e)
}

fn np(name: &str, expr: PolyExpr) -> NamedPoly {
    NamedPoly {
        name: name.into(),
        expr,
        provenance: None,
    }
}

/// R3 Finding 1/2 回帰:
/// (1) 部分変数文脈被覆 `{s,a} ∪ {s,b}`＋分割観測 `oa->a, ob->b` で任意の `ambient_lift` に対して
///     偽 `Undetermined` にならず、零/非零どちらでも Mayer–Vietoris 一致が成立すること（Q および Z）。
/// (2) `raw_read_diff` が相対 lift 存在時に復元 lift `shifted` 上で評価され、非全射 `j_rho` では `None` を返すこと。
#[test]
fn r3_partial_context_relative_reading_and_raw_read_diff_invariance() {
    for domain in [CoeffDomain::Q, CoeffDomain::Z] {
        for (oa_eps, ob_eps, expected_verdict) in
            [(0i64, 0i64, Verdict::Established), (1, 2, Verdict::Refuted)]
        {
            let task = validate_lift_task(LiftTaskSpec {
                name: format!("r3_f1_{oa_eps}_{ob_eps}"),
                coeff_domain: domain.clone(),
                variables: vec!["s".into(), "a".into(), "b".into()],
                ring_params: vec![],
                laws: vec![
                    np("la", sub(sv("a"), sv("s"))),
                    np("lb", sub(sv("b"), sv("s"))),
                ],
                extension: SquareZeroSpec::TruncatedPoly {
                    var_name: "eps".into(),
                    base_degree: 0,
                },
                base_point: vec![
                    ("s".into(), vec![cz(0)]),
                    ("a".into(), vec![cz(0)]),
                    ("b".into(), vec![cz(0)]),
                ],
                ambient_lift: Some(vec![
                    ("s".into(), vec![cz(0), cz(0)]),
                    ("a".into(), vec![cz(0), cz(7)]),
                    ("b".into(), vec![cz(0), cz(-3)]),
                ]),
                relative_reading: Some(RelativeReadingSpec {
                    obs_vars: vec!["oa".into(), "ob".into()],
                    obs_laws: vec![],
                    reading_map: vec![("oa".into(), sv("a")), ("ob".into(), sv("b"))],
                    designated_obs_lift: vec![
                        ("oa".into(), vec![cz(0), cz(oa_eps)]),
                        ("ob".into(), vec![cz(0), cz(ob_eps)]),
                    ],
                    raw_read_diff: None,
                }),
                declaration_cover: Some(DeclarationCoverSpec {
                    contexts: vec![
                        DeclarationContextSpec {
                            name: "left".into(),
                            vars: vec!["s".into(), "a".into()],
                            laws: vec!["la".into()],
                            observations: vec![],
                        },
                        DeclarationContextSpec {
                            name: "right".into(),
                            vars: vec!["s".into(), "b".into()],
                            laws: vec!["lb".into()],
                            observations: vec![],
                        },
                    ],
                    two_context_cech: Some(TwoContextCechSpec {
                        left_context: "left".into(),
                        right_context: "right".into(),
                        shared_vars: vec!["s".into()],
                    }),
                }),
                affine_allowed: None,
                redundant_comparison: None,
                etale_descent: None,
                max_syzygy_pairs: None,
                provenance: prov(vec![MathClause::G141E5, MathClause::G141E7]),
            })
            .unwrap();
            let out = solve_lift_task(&task);
            assert_eq!(out.verdict, expected_verdict);
            let cov = out
                .lift
                .as_ref()
                .unwrap()
                .declaration_cover
                .as_ref()
                .unwrap();
            assert!(cov.support_closed);
            assert_eq!(cov.matches_relative_obstruction, Some(true));
        }
    }

    let recovered_eval = validate_lift_task(LiftTaskSpec {
        name: "r3_f2_restored_eval".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["delta".into(), "mu".into(), "E".into()],
        ring_params: vec![],
        laws: vec![np("e_eq", sub(sv("E"), mul(sv("mu"), sv("delta"))))],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 1,
        },
        base_point: vec![
            ("delta".into(), vec![cz(0), cz(1)]),
            ("mu".into(), vec![cz(0), cz(1)]),
            ("E".into(), vec![cz(0), cz(0)]),
        ],
        ambient_lift: Some(vec![
            ("delta".into(), vec![cz(0), cz(1), cz(0)]),
            ("mu".into(), vec![cz(0), cz(1), cz(0)]),
            ("E".into(), vec![cz(0), cz(0), cz(3)]),
        ]),
        relative_reading: Some(RelativeReadingSpec {
            obs_vars: vec!["delta".into(), "mu".into()],
            obs_laws: vec![],
            reading_map: vec![("delta".into(), sv("delta")), ("mu".into(), sv("mu"))],
            designated_obs_lift: vec![
                ("delta".into(), vec![cz(0), cz(1), cz(0)]),
                ("mu".into(), vec![cz(0), cz(1), cz(0)]),
            ],
            raw_read_diff: Some(RawReadComparisonSpec {
                label: "e_minus_md".into(),
                expr: sub(sv("E"), mul(sv("mu"), sv("delta"))),
                negated: false,
            }),
        }),
        declaration_cover: None,
        affine_allowed: None,
        redundant_comparison: None,
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E5]),
    })
    .unwrap();
    let out_rec = solve_lift_task(&recovered_eval);
    assert_eq!(out_rec.verdict, Verdict::Established);
    let rc_rec = out_rec
        .lift
        .as_ref()
        .unwrap()
        .relative_cone
        .as_ref()
        .unwrap();
    assert_eq!(rc_rec.raw_read_diff_value.as_deref(), Some("0"));
    assert_eq!(rc_rec.raw_read_diff_signed_match, Some(true));

    let nonsurj = validate_lift_task(LiftTaskSpec {
        name: "r3_f2_nonsurj".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["x".into()],
        ring_params: vec![],
        laws: vec![],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 0,
        },
        base_point: vec![("x".into(), vec![cz(0)])],
        ambient_lift: Some(vec![("x".into(), vec![cz(0), cz(0)])]),
        relative_reading: Some(RelativeReadingSpec {
            obs_vars: vec!["w".into()],
            obs_laws: vec![],
            reading_map: vec![("w".into(), pow(sv("x"), 2))],
            designated_obs_lift: vec![("w".into(), vec![cz(0), cz(1)])],
            raw_read_diff: Some(RawReadComparisonSpec {
                label: "x_diff".into(),
                expr: sv("x"),
                negated: false,
            }),
        }),
        declaration_cover: None,
        affine_allowed: None,
        redundant_comparison: None,
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E5]),
    })
    .unwrap();
    let out_ns = solve_lift_task(&nonsurj);
    assert_eq!(out_ns.verdict, Verdict::Refuted);
    let rc_ns = out_ns
        .lift
        .as_ref()
        .unwrap()
        .relative_cone
        .as_ref()
        .unwrap();
    assert_eq!(rc_ns.raw_read_diff_value, None);
    assert_eq!(rc_ns.raw_read_diff_signed_match, None);
}

/// R4 Finding 1/3 回帰:
/// (1) `shared_vars ⊊ left_vars ∩ right_vars` でも全交差上で Čech 判定し偽零・偽陽性を起こさないこと。
/// (2) 3 文脈被覆で `(left, right)` が Law を網羅しない場合は `support_closed == false` となること。
/// (3) 相対 lift 存在下でも `H^0(F_u)` 依存の `raw_read_diff` は `None` を返すこと。
#[test]
fn r4_full_overlap_cech_three_context_completeness_and_h0_raw_diff() {
    let partial_shared = validate_lift_task(LiftTaskSpec {
        name: "r4_partial_shared".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["x".into(), "y".into()],
        ring_params: vec![RingParamSpec {
            name: "t".into(),
            value_in_r_prime: vec![cz(0), cz(1)],
        }],
        laws: vec![
            np("l1", sv("x")),
            np("l2", sub(sv("x"), PolyExpr::ParamVar("t".into()))),
        ],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 0,
        },
        base_point: vec![("x".into(), vec![cz(0)]), ("y".into(), vec![cz(0)])],
        ambient_lift: None,
        relative_reading: Some(RelativeReadingSpec {
            obs_vars: vec![],
            obs_laws: vec![],
            reading_map: vec![],
            designated_obs_lift: vec![],
            raw_read_diff: Some(RawReadComparisonSpec {
                label: "zero_diff".into(),
                expr: cz(0),
                negated: false,
            }),
        }),
        declaration_cover: Some(DeclarationCoverSpec {
            contexts: vec![
                DeclarationContextSpec {
                    name: "left".into(),
                    vars: vec!["x".into(), "y".into()],
                    laws: vec!["l1".into()],
                    observations: vec![],
                },
                DeclarationContextSpec {
                    name: "right".into(),
                    vars: vec!["x".into(), "y".into()],
                    laws: vec!["l2".into()],
                    observations: vec![],
                },
            ],
            two_context_cech: Some(TwoContextCechSpec {
                left_context: "left".into(),
                right_context: "right".into(),
                shared_vars: vec!["y".into()],
            }),
        }),
        affine_allowed: None,
        redundant_comparison: None,
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E5, MathClause::G141E7]),
    })
    .unwrap();
    let out_ps = solve_lift_task(&partial_shared);
    assert_eq!(out_ps.verdict, Verdict::Refuted);
    let d_ps = out_ps.lift.as_ref().unwrap();
    assert_eq!(
        d_ps.declaration_cover
            .as_ref()
            .unwrap()
            .matches_relative_obstruction,
        Some(true)
    );
    assert_eq!(
        d_ps.relative_cone
            .as_ref()
            .unwrap()
            .raw_read_diff_signed_match,
        Some(false)
    );

    let three_ctx = validate_lift_task(LiftTaskSpec {
        name: "r4_three_ctx".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["x".into(), "y".into()],
        ring_params: vec![],
        laws: vec![
            np("l1", sv("x")),
            np("l2", sv("y")),
            np("l3", sub(sv("x"), sv("y"))),
        ],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 0,
        },
        base_point: vec![("x".into(), vec![cz(0)]), ("y".into(), vec![cz(0)])],
        ambient_lift: None,
        relative_reading: None,
        declaration_cover: Some(DeclarationCoverSpec {
            contexts: vec![
                DeclarationContextSpec {
                    name: "C1".into(),
                    vars: vec!["x".into()],
                    laws: vec!["l1".into()],
                    observations: vec![],
                },
                DeclarationContextSpec {
                    name: "C2".into(),
                    vars: vec!["y".into()],
                    laws: vec!["l2".into()],
                    observations: vec![],
                },
                DeclarationContextSpec {
                    name: "C3".into(),
                    vars: vec!["x".into(), "y".into()],
                    laws: vec!["l3".into()],
                    observations: vec![],
                },
            ],
            two_context_cech: Some(TwoContextCechSpec {
                left_context: "C1".into(),
                right_context: "C2".into(),
                shared_vars: vec![],
            }),
        }),
        affine_allowed: None,
        redundant_comparison: None,
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E7]),
    })
    .unwrap();
    let cov3 = solve_lift_task(&three_ctx)
        .lift
        .unwrap()
        .declaration_cover
        .unwrap();
    assert!(!cov3.support_closed);
    assert!(cov3.two_context_cech_diff.is_none());

    let h0_dep = validate_lift_task(LiftTaskSpec {
        name: "r4_h0_dep".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["x".into(), "y".into()],
        ring_params: vec![],
        laws: vec![],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 0,
        },
        base_point: vec![("x".into(), vec![cz(0)]), ("y".into(), vec![cz(0)])],
        ambient_lift: Some(vec![
            ("x".into(), vec![cz(0), cz(0)]),
            ("y".into(), vec![cz(0), cz(3)]),
        ]),
        relative_reading: Some(RelativeReadingSpec {
            obs_vars: vec!["x".into()],
            obs_laws: vec![],
            reading_map: vec![("x".into(), sv("x"))],
            designated_obs_lift: vec![("x".into(), vec![cz(0), cz(0)])],
            raw_read_diff: Some(RawReadComparisonSpec {
                label: "free_y".into(),
                expr: sv("y"),
                negated: false,
            }),
        }),
        declaration_cover: None,
        affine_allowed: None,
        redundant_comparison: None,
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E5]),
    })
    .unwrap();
    let rc_h0 = solve_lift_task(&h0_dep)
        .lift
        .unwrap()
        .relative_cone
        .unwrap();
    assert_eq!(rc_h0.raw_read_diff_value, None);
    assert_eq!(rc_h0.raw_read_diff_signed_match, None);
}
