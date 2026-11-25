//! Step 2 `solver/lift` 監査回帰・H4 証人テスト（F1/F3/F4/F6/F7/F8）。

use crate::ir::change::NamedPoly;
use crate::ir::lift::{
    DeclarationContextSpec, DeclarationCoverSpec, LiftTaskSpec, RawReadComparisonSpec,
    RedundantLawComparisonSpec, RelativeReadingSpec, SquareZeroSpec, TwoContextCechSpec,
    validate_lift_task,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::solver::solve_lift_task;
use num_bigint::BigInt;

fn prov(clauses: Vec<MathClause>) -> Provenance {
    Provenance::new(
        vec![SourceRef::new("test:lift_extra", OriginKind::HumanAdopted)],
        clauses,
    )
}

fn sv(name: &str) -> PolyExpr {
    PolyExpr::StateVar(name.into())
}

fn cz(n: i64) -> PolyExpr {
    PolyExpr::Const(ScalarLit::Z(BigInt::from(n)))
}

fn c_dom(domain: &CoeffDomain, n: i64) -> PolyExpr {
    match domain {
        CoeffDomain::Fp(p) => {
            let p_i64 = i64::try_from(p).unwrap_or(5);
            let rem = n.rem_euclid(p_i64) as u64;
            PolyExpr::Const(ScalarLit::Fp {
                value: rem.into(),
                modulus: p.clone(),
            })
        }
        _ => cz(n),
    }
}

fn sub(a: PolyExpr, b: PolyExpr) -> PolyExpr {
    PolyExpr::Sub(Box::new(a), Box::new(b))
}

fn mul(a: PolyExpr, b: PolyExpr) -> PolyExpr {
    PolyExpr::Mul(Box::new(a), Box::new(b))
}

fn neg(a: PolyExpr) -> PolyExpr {
    PolyExpr::Neg(Box::new(a))
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

/// F1 回帰:
/// (1) 向きを定める二文脈 Čech がない非零相対障害では `raw_read_diff_signed_match` を安易に推測せず `None` とする。
/// (2) 二文脈 Čech があるとき、任意 ambient lift・Law 順序入替・Law 符号反転・冗長 Law 追加のすべてで不変に
///     符号付き一致し、`negated: false` や左右文脈入替では `Some(false)` となる（Q・F_5・線形 Z）。
#[test]
fn f1_h10_raw_read_diff_is_ambient_lift_invariant_without_declaration_cover() {
    // (1) declaration_cover: None では raw_read_diff_value を報告しつつ符号判定は None
    let unoriented = validate_lift_task(LiftTaskSpec {
        name: "h10_unoriented".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["delta".into(), "mu".into(), "E".into()],
        ring_params: vec![],
        laws: vec![
            np("e_zero", sv("E")),
            np("e_eq_mu_delta", sub(sv("E"), mul(sv("mu"), sv("delta")))),
        ],
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
            ("delta".into(), vec![cz(0), cz(1), cz(7)]),
            ("mu".into(), vec![cz(0), cz(1), cz(-5)]),
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
                label: "h10_raw_diff".into(),
                expr: neg(mul(sv("mu"), sv("delta"))),
                negated: true,
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
    let out_u = solve_lift_task(&unoriented);
    assert_eq!(out_u.verdict, Verdict::Refuted);
    let rc_u = out_u.lift.as_ref().unwrap().relative_cone.as_ref().unwrap();
    assert!(!rc_u.relative_obstruction_is_zero);
    assert_eq!(rc_u.raw_read_diff_value.as_deref(), Some("-eps^2"));
    assert_eq!(rc_u.raw_read_diff_signed_match, None);

    // (2) Law 順入替・Law 符号反転・冗長 Law 追加・任意 ambient lift・左右文脈入替の厳密検証
    let law_variants = [
        (
            "canonical",
            vec![
                np("e_zero", sv("E")),
                np("e_eq", sub(sv("E"), mul(sv("mu"), sv("delta")))),
            ],
            vec!["e_zero"],
            vec!["e_eq"],
        ),
        (
            "reordered",
            vec![
                np("e_eq", sub(sv("E"), mul(sv("mu"), sv("delta")))),
                np("e_zero", sv("E")),
            ],
            vec!["e_zero"],
            vec!["e_eq"],
        ),
        (
            "sign_flipped",
            vec![
                np("e_zero", neg(sv("E"))),
                np("e_eq", sub(sv("E"), mul(sv("mu"), sv("delta")))),
            ],
            vec!["e_zero"],
            vec!["e_eq"],
        ),
        (
            "redundant_law",
            vec![
                np("e_zero", sv("E")),
                np("e_zero_dup", sv("E")),
                np("e_eq", sub(sv("E"), mul(sv("mu"), sv("delta")))),
            ],
            vec!["e_zero", "e_zero_dup"],
            vec!["e_eq"],
        ),
    ];
    for domain in [CoeffDomain::Q, CoeffDomain::Fp(5u32.into())] {
        for (tag, laws, left_laws, right_laws) in &law_variants {
            for (negated, swap_lr, expected_match) in [
                (true, false, true),
                (false, false, false),
                (true, true, false),
            ] {
                let (l_name, r_name) = if swap_lr {
                    ("ctx_eq", "ctx_zero")
                } else {
                    ("ctx_zero", "ctx_eq")
                };
                let task = validate_lift_task(LiftTaskSpec {
                    name: format!("h10_f1_{tag}_{negated}_{swap_lr}"),
                    coeff_domain: domain.clone(),
                    variables: vec!["delta".into(), "mu".into(), "E".into()],
                    ring_params: vec![],
                    laws: laws.clone(),
                    extension: SquareZeroSpec::TruncatedPoly {
                        var_name: "eps".into(),
                        base_degree: 1,
                    },
                    base_point: vec![
                        ("delta".into(), vec![c_dom(&domain, 0), c_dom(&domain, 1)]),
                        ("mu".into(), vec![c_dom(&domain, 0), c_dom(&domain, 1)]),
                        ("E".into(), vec![c_dom(&domain, 0), c_dom(&domain, 0)]),
                    ],
                    ambient_lift: Some(vec![
                        (
                            "delta".into(),
                            vec![c_dom(&domain, 0), c_dom(&domain, 1), c_dom(&domain, 7)],
                        ),
                        (
                            "mu".into(),
                            vec![c_dom(&domain, 0), c_dom(&domain, 1), c_dom(&domain, -5)],
                        ),
                        (
                            "E".into(),
                            vec![c_dom(&domain, 0), c_dom(&domain, 0), c_dom(&domain, 3)],
                        ),
                    ]),
                    relative_reading: Some(RelativeReadingSpec {
                        obs_vars: vec!["delta".into(), "mu".into()],
                        obs_laws: vec![],
                        reading_map: vec![
                            ("delta".into(), sv("delta")),
                            ("mu".into(), sv("mu")),
                        ],
                        designated_obs_lift: vec![
                            (
                                "delta".into(),
                                vec![c_dom(&domain, 0), c_dom(&domain, 1), c_dom(&domain, 0)],
                            ),
                            (
                                "mu".into(),
                                vec![c_dom(&domain, 0), c_dom(&domain, 1), c_dom(&domain, 0)],
                            ),
                        ],
                        raw_read_diff: Some(RawReadComparisonSpec {
                            label: "h10_raw_diff".into(),
                            expr: neg(mul(sv("mu"), sv("delta"))),
                            negated,
                        }),
                    }),
                    declaration_cover: Some(DeclarationCoverSpec {
                        contexts: vec![
                            DeclarationContextSpec {
                                name: "ctx_zero".into(),
                                vars: vec!["delta".into(), "mu".into(), "E".into()],
                                laws: left_laws.iter().map(|s| (*s).to_owned()).collect(),
                                observations: vec![],
                            },
                            DeclarationContextSpec {
                                name: "ctx_eq".into(),
                                vars: vec!["delta".into(), "mu".into(), "E".into()],
                                laws: right_laws.iter().map(|s| (*s).to_owned()).collect(),
                                observations: vec![],
                            },
                        ],
                        two_context_cech: Some(TwoContextCechSpec {
                            left_context: l_name.into(),
                            right_context: r_name.into(),
                            shared_vars: vec!["E".into()],
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
                assert_eq!(out.verdict, Verdict::Refuted);
                let d = out.lift.as_ref().unwrap();
                let rc = d.relative_cone.as_ref().unwrap();
                assert!(!rc.relative_obstruction_is_zero);
                assert_eq!(rc.raw_read_diff_signed_match, Some(expected_match));
                let cov = d.declaration_cover.as_ref().unwrap();
                assert_eq!(cov.matches_relative_obstruction, Some(true));
            }
        }
    }

    // Z 上の線形相対 cone + 二文脈 Čech でも任意 ambient lift で厳密一致
    for (negated, expected_match) in [(true, true), (false, false)] {
        let task_z = validate_lift_task(LiftTaskSpec {
            name: format!("z_rel_f1_{negated}"),
            coeff_domain: CoeffDomain::Z,
            variables: vec!["delta".into(), "E".into()],
            ring_params: vec![],
            laws: vec![
                np("e_eq_delta", sub(sv("E"), sv("delta"))),
                np("e_zero", sv("E")),
            ],
            extension: SquareZeroSpec::TruncatedPoly {
                var_name: "eps".into(),
                base_degree: 0,
            },
            base_point: vec![("delta".into(), vec![cz(0)]), ("E".into(), vec![cz(0)])],
            ambient_lift: Some(vec![
                ("delta".into(), vec![cz(0), cz(7)]),
                ("E".into(), vec![cz(0), cz(3)]),
            ]),
            relative_reading: Some(RelativeReadingSpec {
                obs_vars: vec!["delta".into()],
                obs_laws: vec![],
                reading_map: vec![("delta".into(), sv("delta"))],
                designated_obs_lift: vec![("delta".into(), vec![cz(0), cz(1)])],
                raw_read_diff: Some(RawReadComparisonSpec {
                    label: "z_raw_diff".into(),
                    expr: neg(sv("delta")),
                    negated,
                }),
            }),
            declaration_cover: Some(DeclarationCoverSpec {
                contexts: vec![
                    DeclarationContextSpec {
                        name: "ctx_zero".into(),
                        vars: vec!["delta".into(), "E".into()],
                        laws: vec!["e_zero".into()],
                        observations: vec![],
                    },
                    DeclarationContextSpec {
                        name: "ctx_eq".into(),
                        vars: vec!["delta".into(), "E".into()],
                        laws: vec!["e_eq_delta".into()],
                        observations: vec![],
                    },
                ],
                two_context_cech: Some(TwoContextCechSpec {
                    left_context: "ctx_zero".into(),
                    right_context: "ctx_eq".into(),
                    shared_vars: vec!["E".into()],
                }),
            }),
            affine_allowed: None,
            redundant_comparison: None,
            etale_descent: None,
            max_syzygy_pairs: None,
            provenance: prov(vec![MathClause::G141E5, MathClause::G141E7]),
        })
        .unwrap();
        let out = solve_lift_task(&task_z);
        assert_eq!(out.verdict, Verdict::Refuted);
        let d = out.lift.as_ref().unwrap();
        let rc = d.relative_cone.as_ref().unwrap();
        assert!(!rc.relative_obstruction_is_zero);
        assert_eq!(rc.raw_read_diff_signed_match, Some(expected_match));
        assert_eq!(
            d.declaration_cover
                .as_ref()
                .unwrap()
                .matches_relative_obstruction,
            Some(true)
        );
    }
}

/// F3 回帰: Z 上の `redundant_comparison` が `H^1` torsion 差異（`[2x]` vs `[x]`）を
/// `free_rank == 0` だけで同一視せず `h1_matches == false` と判定すること。
#[test]
fn f3_z_redundant_comparison_distinguishes_h1_torsion() {
    let task = validate_lift_task(LiftTaskSpec {
        name: "z_h1_torsion_diff".into(),
        coeff_domain: CoeffDomain::Z,
        variables: vec!["x".into()],
        ring_params: vec![],
        laws: vec![np("two_x", mul(cz(2), sv("x")))],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 0,
        },
        base_point: vec![("x".into(), vec![cz(0)])],
        ambient_lift: Some(vec![("x".into(), vec![cz(0), cz(0)])]),
        relative_reading: None,
        declaration_cover: None,
        affine_allowed: None,
        redundant_comparison: Some(RedundantLawComparisonSpec {
            reference_laws: vec![np("one_x", sv("x"))],
        }),
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E2]),
    })
    .unwrap();
    let out = solve_lift_task(&task);
    assert_eq!(out.verdict, Verdict::Established);
    let red = out
        .lift
        .as_ref()
        .unwrap()
        .redundant_comparison
        .as_ref()
        .unwrap();
    assert!(!red.h1_matches);
    assert!(red.h0_matches);
}

/// F4 回帰: 宣言被覆の支持閉包検査が文脈内 `laws` の外部変数参照を検出すること（E7/E8）。
#[test]
fn f4_declaration_cover_detects_unclosed_law_variable_reference() {
    let task = validate_lift_task(LiftTaskSpec {
        name: "e7_unclosed_law".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["X".into(), "Y".into(), "T".into()],
        ring_params: vec![],
        laws: vec![np("sum_law", sub(sv("T"), PolyExpr::Add(Box::new(sv("X")), Box::new(sv("Y")))))],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 0,
        },
        base_point: vec![
            ("X".into(), vec![cz(0)]),
            ("Y".into(), vec![cz(0)]),
            ("T".into(), vec![cz(0)]),
        ],
        ambient_lift: None,
        relative_reading: None,
        declaration_cover: Some(DeclarationCoverSpec {
            contexts: vec![DeclarationContextSpec {
                name: "partial_ctx".into(),
                vars: vec!["X".into(), "T".into()],
                laws: vec!["sum_law".into()],
                observations: vec![],
            }],
            two_context_cech: None,
        }),
        affine_allowed: None,
        redundant_comparison: None,
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E7]),
    })
    .unwrap();
    let out = solve_lift_task(&task);
    let cov = out
        .lift
        .as_ref()
        .unwrap()
        .declaration_cover
        .as_ref()
        .unwrap();
    assert!(!cov.support_closed);
    assert!(
        cov.unclosed_observations
            .iter()
            .any(|s| s.contains("partial_ctx.law:sum_law") && s.contains('Y'))
    );
}

/// F6 回帰: `redundant_comparison.reference_laws` が基点で零にならない場合、
/// `ApplicabilityConditionNotMet` で沈黙すること。
#[test]
fn f6_redundant_comparison_silences_when_reference_law_nonzero_at_base() {
    let task = validate_lift_task(LiftTaskSpec {
        name: "ref_law_bad_base".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["x".into()],
        ring_params: vec![],
        laws: vec![np("x_eq_0", sv("x"))],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 0,
        },
        base_point: vec![("x".into(), vec![cz(0)])],
        ambient_lift: None,
        relative_reading: None,
        declaration_cover: None,
        affine_allowed: None,
        redundant_comparison: Some(RedundantLawComparisonSpec {
            reference_laws: vec![np("x_minus_1", sub(sv("x"), cz(1)))],
        }),
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E2]),
    })
    .unwrap();
    let out = solve_lift_task(&task);
    assert!(matches!(
        out.verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { .. })
    ));
}

/// F7 回帰: 0 変数観測（`obs_vars = []`, `obs_laws = [0]`）の相対 cone が
/// `ArityMismatch` で落ちず正常計算されること。
#[test]
fn f7_relative_cone_handles_empty_obs_vars_with_constant_obs_law() {
    let task = validate_lift_task(LiftTaskSpec {
        name: "empty_obs_vars_rel_cone".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["x".into()],
        ring_params: vec![],
        laws: vec![np("x_zero", sv("x"))],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 0,
        },
        base_point: vec![("x".into(), vec![cz(0)])],
        ambient_lift: None,
        relative_reading: Some(RelativeReadingSpec {
            obs_vars: vec![],
            obs_laws: vec![np("const_zero", cz(0))],
            reading_map: vec![],
            designated_obs_lift: vec![],
            raw_read_diff: None,
        }),
        declaration_cover: None,
        affine_allowed: None,
        redundant_comparison: None,
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E4]),
    })
    .unwrap();
    let out = solve_lift_task(&task);
    assert_eq!(out.verdict, Verdict::Established);
    let rc = out.lift.as_ref().unwrap().relative_cone.as_ref().unwrap();
    assert!(rc.relative_obstruction_is_zero);
}

/// F8: H4 証人（`Y = T^2`, `Y = 0`）の `solve_lift_task` 相対 cone＋二文脈 Čech 試験。
/// 任意の一次観測 lift `T' = eps + a*eps^2`（`a = 0, 1, -3`）で相対障害非零・
/// 二文脈 Čech 差 `+eps^2` 一致・`raw_read_diff = -T^2` 負号一致を確認する（AC3(d)・H4）。
#[test]
fn f8_h4_quadratic_witness_relative_cone_and_two_context_cech() {
    for a in [0i64, 1, -3] {
        let task = validate_lift_task(LiftTaskSpec {
            name: format!("h4_lift_a_{a}"),
            coeff_domain: CoeffDomain::Q,
            variables: vec!["T".into(), "Y".into()],
            ring_params: vec![],
            laws: vec![
                np("y_zero", sv("Y")),
                np("y_eq_t2", sub(sv("Y"), pow(sv("T"), 2))),
            ],
            extension: SquareZeroSpec::TruncatedPoly {
                var_name: "eps".into(),
                base_degree: 1,
            },
            base_point: vec![
                ("T".into(), vec![cz(0), cz(1)]),
                ("Y".into(), vec![cz(0), cz(0)]),
            ],
            ambient_lift: Some(vec![
                ("T".into(), vec![cz(0), cz(1), cz(a)]),
                ("Y".into(), vec![cz(0), cz(0), cz(5)]),
            ]),
            relative_reading: Some(RelativeReadingSpec {
                obs_vars: vec!["T".into()],
                obs_laws: vec![],
                reading_map: vec![("T".into(), sv("T"))],
                designated_obs_lift: vec![("T".into(), vec![cz(0), cz(1), cz(a)])],
                raw_read_diff: Some(RawReadComparisonSpec {
                    label: "h4_raw_diff".into(),
                    expr: neg(pow(sv("T"), 2)),
                    negated: true,
                }),
            }),
            declaration_cover: Some(DeclarationCoverSpec {
                contexts: vec![
                    DeclarationContextSpec {
                        name: "ctx_zero".into(),
                        vars: vec!["T".into(), "Y".into()],
                        laws: vec!["y_zero".into()],
                        observations: vec![],
                    },
                    DeclarationContextSpec {
                        name: "ctx_quad".into(),
                        vars: vec!["T".into(), "Y".into()],
                        laws: vec!["y_eq_t2".into()],
                        observations: vec![],
                    },
                ],
                two_context_cech: Some(TwoContextCechSpec {
                    left_context: "ctx_zero".into(),
                    right_context: "ctx_quad".into(),
                    shared_vars: vec!["Y".into()],
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
        assert_eq!(out.verdict, Verdict::Refuted);
        let d = out.lift.as_ref().unwrap();
        let rc = d.relative_cone.as_ref().unwrap();
        assert!(!rc.relative_obstruction_is_zero);
        assert_eq!(rc.raw_read_diff_signed_match, Some(true));
        let cov = d.declaration_cover.as_ref().unwrap();
        assert!(cov.support_closed);
        assert_eq!(cov.matches_relative_obstruction, Some(true));
        let diff = cov.two_context_cech_diff.as_ref().unwrap();
        assert_eq!(diff.get("Y").map(String::as_str), Some("eps^2"));
    }
}

/// R2 Finding 2/3 回帰:
/// (1) 非 étale 被覆（`base_invertible: false` および `CoeffDomain::Z`）が `ApplicabilityConditionNotMet` で沈黙する。
/// (2) E7 宣言被覆で宣言変数または Law が被覆全体から欠落していれば `support_closed == false` となる。
#[test]
fn r2_etale_non_applicable_silences_and_e7_checks_covering_completeness() {
    use crate::ir::lift::FiniteEtaleDescentSpec;

    for (domain, base_inv) in [(CoeffDomain::Q, false), (CoeffDomain::Z, true)] {
        let task = validate_lift_task(LiftTaskSpec {
            name: format!("non_etale_{base_inv}"),
            coeff_domain: domain,
            variables: vec!["t".into()],
            ring_params: vec![],
            laws: vec![],
            extension: SquareZeroSpec::TruncatedPoly {
                var_name: "eps".into(),
                base_degree: 0,
            },
            base_point: vec![("t".into(), vec![cz(1)])],
            ambient_lift: None,
            relative_reading: None,
            declaration_cover: None,
            affine_allowed: None,
            redundant_comparison: None,
            etale_descent: Some(FiniteEtaleDescentSpec {
                base_var: "t".into(),
                cover_var: "z".into(),
                degree: 2,
                base_invertible: base_inv,
            }),
            max_syzygy_pairs: None,
            provenance: prov(vec![MathClause::G141C9]),
        })
        .unwrap();
        assert!(matches!(
            solve_lift_task(&task).verdict,
            Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { .. })
        ));
    }

    // E7: sum_law を省いた被覆や空被覆は support_closed == false
    let incomplete_cover = validate_lift_task(LiftTaskSpec {
        name: "e7_missing_law_in_cover".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["X".into(), "Y".into(), "T".into()],
        ring_params: vec![],
        laws: vec![np(
            "sum_law",
            sub(sv("T"), PolyExpr::Add(Box::new(sv("X")), Box::new(sv("Y")))),
        )],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 0,
        },
        base_point: vec![
            ("X".into(), vec![cz(0)]),
            ("Y".into(), vec![cz(0)]),
            ("T".into(), vec![cz(0)]),
        ],
        ambient_lift: None,
        relative_reading: None,
        declaration_cover: Some(DeclarationCoverSpec {
            contexts: vec![
                DeclarationContextSpec {
                    name: "ctx_x".into(),
                    vars: vec!["X".into()],
                    laws: vec![],
                    observations: vec![],
                },
                DeclarationContextSpec {
                    name: "ctx_y".into(),
                    vars: vec!["Y".into()],
                    laws: vec![],
                    observations: vec![],
                },
            ],
            two_context_cech: None,
        }),
        affine_allowed: None,
        redundant_comparison: None,
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E7]),
    })
    .unwrap();
    let cov = solve_lift_task(&incomplete_cover)
        .lift
        .unwrap()
        .declaration_cover
        .unwrap();
    assert!(!cov.support_closed);
    assert!(
        cov.unclosed_observations
            .iter()
            .any(|s| s == "uncovered_var:T")
    );
    assert!(
        cov.unclosed_observations
            .iter()
            .any(|s| s == "uncovered_law:sum_law")
    );
}

/// R3 Finding 1/2 回帰:
/// (1) 部分変数文脈被覆 `{s,a} ∪ {s,b}`＋分割観測 `oa->a, ob->b` で任意の `ambient_lift` に対して
///     偽 `Undetermined` にならず、零/非零どちらでも Mayer–Vietoris 一致が成立すること（Q および Z）。
/// (2) `raw_read_diff` が相対 lift 存在時に復元 lift `shifted` 上で評価され、非全射 `j_rho` や
///     `ker(j_rho)` 依存式では黙ってフォールバックせず `None` を返すこと。
#[test]
fn r3_partial_context_relative_reading_and_raw_read_diff_invariance() {
    // (1) Finding 1 反例: variables=[s,a,b], laws=[a-s, b-s], left={s,a}, right={s,b}, obs=[oa->a, ob->b]
    for domain in [CoeffDomain::Q, CoeffDomain::Z] {
        for (oa_eps, ob_eps, expected_verdict) in [
            (0i64, 0i64, Verdict::Established),
            (1, 2, Verdict::Refuted),
        ] {
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

    // (2a) Finding 2 反例 1: 相対 lift 存在時に `raw_read_diff = E - mu*delta` を復元 lift で評価
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

    // (2b) Finding 2 反例 2: 非全射 j_rho (w -> x^2, w = eps) では無警告フォールバックせず None
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
    let rc_ns = out_ns.lift.as_ref().unwrap().relative_cone.as_ref().unwrap();
    assert_eq!(rc_ns.raw_read_diff_value, None);
    assert_eq!(rc_ns.raw_read_diff_signed_match, None);
}
