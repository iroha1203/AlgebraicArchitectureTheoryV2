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

/// F1 回帰: H10 の `raw_read_diff` が `declaration_cover: None` かつ任意の ambient lift
/// （例: `E = 3*eps^2`, `delta = eps + 7*eps^2`）に対して不変に符号付き一致し、
/// 符号を反転（`negated: false`）すると `false` になること（Q・F_5、および線形 Z 系）。
#[test]
fn f1_h10_raw_read_diff_is_ambient_lift_invariant_without_declaration_cover() {
    for domain in [CoeffDomain::Q, CoeffDomain::Fp(5u32.into())] {
        for (ambient_e, ambient_d_eps2, negated, expected_match) in [
            (0i64, 0i64, true, true),
            (3, 7, true, true),
            (-4, 2, true, true),
            (3, 7, false, false),
        ] {
            let task = validate_lift_task(LiftTaskSpec {
                name: format!("h10_f1_{ambient_e}_{negated}"),
                coeff_domain: domain.clone(),
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
                    ("delta".into(), vec![c_dom(&domain, 0), c_dom(&domain, 1)]),
                    ("mu".into(), vec![c_dom(&domain, 0), c_dom(&domain, 1)]),
                    ("E".into(), vec![c_dom(&domain, 0), c_dom(&domain, 0)]),
                ],
                ambient_lift: Some(vec![
                    (
                        "delta".into(),
                        vec![
                            c_dom(&domain, 0),
                            c_dom(&domain, 1),
                            c_dom(&domain, ambient_d_eps2),
                        ],
                    ),
                    (
                        "mu".into(),
                        vec![c_dom(&domain, 0), c_dom(&domain, 1), c_dom(&domain, -5)],
                    ),
                    (
                        "E".into(),
                        vec![
                            c_dom(&domain, 0),
                            c_dom(&domain, 0),
                            c_dom(&domain, ambient_e),
                        ],
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
                declaration_cover: None,
                affine_allowed: None,
                redundant_comparison: None,
                etale_descent: None,
                max_syzygy_pairs: None,
                provenance: prov(vec![MathClause::G141E5]),
            })
            .unwrap();
            let out = solve_lift_task(&task);
            assert_eq!(out.verdict, Verdict::Refuted);
            let rc = out.lift.as_ref().unwrap().relative_cone.as_ref().unwrap();
            assert!(!rc.relative_obstruction_is_zero);
            assert_eq!(rc.raw_read_diff_signed_match, Some(expected_match));
        }
    }

    // Z 上の線形相対 cone でも任意の ambient lift に対して obs 整列＋不変判定が成立する。
    for (ambient_e, ambient_d, negated, expected_match) in
        [(3i64, 7i64, true, true), (3, 7, false, false)]
    {
        let task_z = validate_lift_task(LiftTaskSpec {
            name: format!("z_rel_f1_{ambient_e}_{negated}"),
            coeff_domain: CoeffDomain::Z,
            variables: vec!["delta".into(), "E".into()],
            ring_params: vec![],
            laws: vec![
                np("e_zero", sv("E")),
                np("e_eq_delta", sub(sv("E"), sv("delta"))),
            ],
            extension: SquareZeroSpec::TruncatedPoly {
                var_name: "eps".into(),
                base_degree: 0,
            },
            base_point: vec![("delta".into(), vec![cz(0)]), ("E".into(), vec![cz(0)])],
            ambient_lift: Some(vec![
                ("delta".into(), vec![cz(0), cz(ambient_d)]),
                ("E".into(), vec![cz(0), cz(ambient_e)]),
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
            declaration_cover: None,
            affine_allowed: None,
            redundant_comparison: None,
            etale_descent: None,
            max_syzygy_pairs: None,
            provenance: prov(vec![MathClause::G141E5]),
        })
        .unwrap();
        let out = solve_lift_task(&task_z);
        assert_eq!(out.verdict, Verdict::Refuted);
        let rc = out.lift.as_ref().unwrap().relative_cone.as_ref().unwrap();
        assert!(!rc.relative_obstruction_is_zero);
        assert_eq!(rc.raw_read_diff_signed_match, Some(expected_match));
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
