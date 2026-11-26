//! Step 2 `solver/lift` 単体・パラメトリック・沈黙テスト（G-141 E1–E8・C8–C9・H1–H4・H10・W5 / AC3・AC7）。

use crate::ir::change::NamedPoly;
use crate::ir::lift::{
    AffineAllowedSpec, DeclarationContextSpec, DeclarationCoverSpec, FiniteEtaleDescentSpec,
    LiftTaskSpec, RawReadComparisonSpec, RedundantLawComparisonSpec, RelativeReadingSpec,
    RingParamSpec, SquareZeroSpec, TwoContextCechSpec, validate_lift_task,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::solver::solve_lift_task;
use num_bigint::{BigInt, BigUint};

fn prov(clauses: Vec<MathClause>) -> Provenance {
    Provenance::new(
        vec![SourceRef::new("test:lift", OriginKind::HumanAdopted)],
        clauses,
    )
}

fn sv(name: &str) -> PolyExpr {
    PolyExpr::StateVar(name.into())
}

fn pv(name: &str) -> PolyExpr {
    PolyExpr::ParamVar(name.into())
}

fn cz(n: i64) -> PolyExpr {
    PolyExpr::Const(ScalarLit::Z(BigInt::from(n)))
}

fn cfp(v: u32, p: u32) -> PolyExpr {
    PolyExpr::Const(ScalarLit::Fp {
        value: BigUint::from(v),
        modulus: BigUint::from(p),
    })
}

fn sub(a: PolyExpr, b: PolyExpr) -> PolyExpr {
    PolyExpr::Sub(Box::new(a), Box::new(b))
}

fn add(a: PolyExpr, b: PolyExpr) -> PolyExpr {
    PolyExpr::Add(Box::new(a), Box::new(b))
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

#[test]
fn lift_h1_affine_repair_full_fixed_d_and_all_fixed() {
    // H1: c + d - 1 = 0（R' = Q[eps]/(eps^2) -> R = Q）。
    // 基点 (c, d) = (1, 0) は R 上で合法。ambient_lift = (1 + eps, 0) で残差 eps を発生させ、
    // 許容部分加群 H = {(Δc, Δd)}, {(Δc, 0)}, {(0, 0)} を比較する。
    let make_spec = |allowed: Vec<&str>, finite: bool| LiftTaskSpec {
        name: "h1_affine".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["c".into(), "d".into()],
        ring_params: vec![],
        laws: vec![np("sum_one", sub(add(sv("c"), sv("d")), cz(1)))],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 0,
        },
        base_point: vec![("c".into(), vec![cz(1)]), ("d".into(), vec![cz(0)])],
        ambient_lift: Some(vec![
            ("c".into(), vec![cz(1), cz(1)]),
            ("d".into(), vec![cz(0), cz(0)]),
        ]),
        relative_reading: None,
        declaration_cover: None,
        affine_allowed: Some(AffineAllowedSpec {
            allowed_vars: allowed.into_iter().map(str::to_owned).collect(),
            finite_displacement: finite,
        }),
        redundant_comparison: None,
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E6]),
    };

    // (1) 全域 (c, d) 許可（有限変位 & 無限小変位の双方）: 修復存在・1 自由度 torsor・再評価一致
    for finite in [false, true] {
        let task = validate_lift_task(make_spec(vec!["c", "d"], finite)).unwrap();
        let out = solve_lift_task(&task);
        assert_eq!(out.verdict, Verdict::Established);
        let detail = out.lift.unwrap();
        assert!(detail.complex_d1_d0_zero_verified);
        assert!(detail.residual_cocycle_verified);
        let aff = detail.affine_repair.unwrap();
        assert!(aff.repair_exists);
        assert_eq!(aff.torsor_basis.len(), if finite { 2 } else { 1 });
        assert!(aff.reevaluation.unwrap().matched);
    }

    // (2) Δd = 0 (c のみ許可): 一意修復 Δc = -eps（torsor 0 次元）・再評価一致
    let task_c = validate_lift_task(make_spec(vec!["c"], false)).unwrap();
    let out_c = solve_lift_task(&task_c);
    assert_eq!(out_c.verdict, Verdict::Established);
    let aff_c = out_c.lift.unwrap().affine_repair.unwrap();
    assert!(aff_c.repair_exists);
    assert!(aff_c.torsor_basis.is_empty());
    assert_eq!(aff_c.particular_delta.unwrap().get("c").unwrap(), "-eps");
    assert!(aff_c.reevaluation.unwrap().matched);

    // (3) 全固定 (allowed = []): 残差 eps != 0 のため修復不能
    let task_empty = validate_lift_task(make_spec(vec![], false)).unwrap();
    let out_empty = solve_lift_task(&task_empty);
    assert_eq!(out_empty.verdict, Verdict::Refuted);
    let aff_empty = out_empty.lift.unwrap().affine_repair.unwrap();
    assert!(!aff_empty.repair_exists);
    assert!(aff_empty.particular_delta.is_none());
}

#[test]
fn lift_h2_quadratic_obstruction_and_redundant_laws_over_q_z_f2() {
    // H2 (Q): t^2 = 0 vs (t^2, t^3) over Q[eps]/(eps^3) -> Q[eps]/(eps^2), base t = eps
    let task_q = validate_lift_task(LiftTaskSpec {
        name: "h2_q_redundant".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["t".into()],
        ring_params: vec![],
        laws: vec![np("t2", pow(sv("t"), 2)), np("t3", pow(sv("t"), 3))],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 1,
        },
        base_point: vec![("t".into(), vec![cz(0), cz(1)])],
        ambient_lift: Some(vec![("t".into(), vec![cz(0), cz(1), cz(0)])]),
        relative_reading: None,
        declaration_cover: None,
        affine_allowed: None,
        redundant_comparison: Some(RedundantLawComparisonSpec {
            reference_laws: vec![np("t2_only", pow(sv("t"), 2))],
        }),
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E2]),
    })
    .unwrap();
    let out_q = solve_lift_task(&task_q);
    assert_eq!(out_q.verdict, Verdict::Refuted);
    let d_q = out_q.lift.unwrap();
    assert!(!d_q.lift_exists);
    assert!(!d_q.obstruction_is_zero);
    assert_eq!(d_q.h0_dim, 1);
    assert_eq!(d_q.h1_dim, 1);
    assert!(d_q.syzygy_identity_verified);
    let red_q = d_q.redundant_comparison.unwrap();
    assert!(red_q.h0_matches && red_q.h1_matches && red_q.obstruction_matches);
    // 冗長 t^3 により T_raw は H^1 = 2 だが全 syzygy D は H^1 = 1
    let raw_q = d_q.raw_cech_comparison.unwrap();
    assert_eq!(raw_q.h1_t_raw_dim, 2);
    assert_eq!(raw_q.h1_d_dim, 1);
    assert!(raw_q.kernel_map_exact_verified && raw_q.differs_from_full_syzygy);

    // 対照: t = 0 (一次) は 1 次自由度なし (h0_dim = 0) かつ lift 存在
    let task_lin = validate_lift_task(LiftTaskSpec {
        name: "h2_linear_contrast".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["t".into()],
        ring_params: vec![],
        laws: vec![np("t_zero", sv("t"))],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 0,
        },
        base_point: vec![("t".into(), vec![cz(0)])],
        ambient_lift: None,
        relative_reading: None,
        declaration_cover: None,
        affine_allowed: None,
        redundant_comparison: None,
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E2]),
    })
    .unwrap();
    let out_lin = solve_lift_task(&task_lin);
    assert_eq!(out_lin.verdict, Verdict::Established);
    let d_lin = out_lin.lift.unwrap();
    assert_eq!(d_lin.h0_dim, 0);
    assert!(d_lin.lift_exists);
    assert!(d_lin.reevaluation.unwrap().matched);

    // H2 (Z): (z^2, 2*z^2) vs (z^2) over Z[eps]/(eps^3) -> Z[eps]/(eps^2)
    let task_z = validate_lift_task(LiftTaskSpec {
        name: "h2_z_redundant".into(),
        coeff_domain: CoeffDomain::Z,
        variables: vec!["z".into()],
        ring_params: vec![],
        laws: vec![
            np("z2", pow(sv("z"), 2)),
            np("two_z2", mul(cz(2), pow(sv("z"), 2))),
        ],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 1,
        },
        base_point: vec![("z".into(), vec![cz(0), cz(1)])],
        ambient_lift: Some(vec![("z".into(), vec![cz(0), cz(1), cz(0)])]),
        relative_reading: None,
        declaration_cover: None,
        affine_allowed: None,
        redundant_comparison: Some(RedundantLawComparisonSpec {
            reference_laws: vec![np("z2_only", pow(sv("z"), 2))],
        }),
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E2]),
    })
    .unwrap();
    let out_z = solve_lift_task(&task_z);
    assert_eq!(out_z.verdict, Verdict::Refuted);
    let red_z = out_z.lift.unwrap().redundant_comparison.unwrap();
    assert!(red_z.h0_matches && red_z.h1_matches && red_z.obstruction_matches);

    // H2 (F_2): (z^2, 0*z^2) vs (z^2) over F_2[eps]/(eps^3) -> F_2[eps]/(eps^2)
    let task_f2 = validate_lift_task(LiftTaskSpec {
        name: "h2_f2_redundant".into(),
        coeff_domain: CoeffDomain::Fp(BigUint::from(2u32)),
        variables: vec!["z".into()],
        ring_params: vec![],
        laws: vec![
            np("z2", pow(sv("z"), 2)),
            np("two_z2", mul(cfp(0, 2), pow(sv("z"), 2))),
        ],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 1,
        },
        base_point: vec![("z".into(), vec![cfp(0, 2), cfp(1, 2)])],
        ambient_lift: Some(vec![("z".into(), vec![cfp(0, 2), cfp(1, 2), cfp(0, 2)])]),
        relative_reading: None,
        declaration_cover: None,
        affine_allowed: None,
        redundant_comparison: Some(RedundantLawComparisonSpec {
            reference_laws: vec![np("z2_only", pow(sv("z"), 2))],
        }),
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E2]),
    })
    .unwrap();
    let out_f2 = solve_lift_task(&task_f2);
    assert_eq!(out_f2.verdict, Verdict::Refuted);
    let red_f2 = out_f2.lift.unwrap().redundant_comparison.unwrap();
    assert!(red_f2.h0_matches && red_f2.h1_matches && red_f2.obstruction_matches);
}

#[test]
fn lift_h3_separates_h1_t_raw_from_h1_full_syzygy_d() {
    // Case A: (x1 - x0, x2 - x1, x0 - x2) => syzygy (1,1,1) により H^1(D) = 0, H^1(T_raw) = 1
    let task_a = validate_lift_task(LiftTaskSpec {
        name: "h3_dependent".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["x0".into(), "x1".into(), "x2".into()],
        ring_params: vec![],
        laws: vec![
            np("f1", sub(sv("x1"), sv("x0"))),
            np("f2", sub(sv("x2"), sv("x1"))),
            np("f3", sub(sv("x0"), sv("x2"))),
        ],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 0,
        },
        base_point: vec![
            ("x0".into(), vec![cz(0)]),
            ("x1".into(), vec![cz(0)]),
            ("x2".into(), vec![cz(0)]),
        ],
        ambient_lift: None,
        relative_reading: None,
        declaration_cover: None,
        affine_allowed: None,
        redundant_comparison: None,
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E8]),
    })
    .unwrap();
    let out_a = solve_lift_task(&task_a);
    assert_eq!(out_a.verdict, Verdict::Established);
    let da = out_a.lift.unwrap();
    assert_eq!(da.h0_dim, 1);
    assert_eq!(da.h1_dim, 0);
    let raw_a = da.raw_cech_comparison.unwrap();
    assert_eq!(raw_a.h1_t_raw_dim, 1);
    assert_eq!(raw_a.h1_d_dim, 0);
    assert!(raw_a.kernel_map_exact_verified && raw_a.differs_from_full_syzygy);

    // Case B: (x1 - x0, x2 - x1, x0 - x2 - t) with t = eps => regular sequence, H^1(D) = 1, 非零障害 [-t]
    let task_b = validate_lift_task(LiftTaskSpec {
        name: "h3_regular_deformed".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["x0".into(), "x1".into(), "x2".into()],
        ring_params: vec![RingParamSpec {
            name: "t".into(),
            value_in_r_prime: vec![cz(0), cz(1)],
        }],
        laws: vec![
            np("f1", sub(sv("x1"), sv("x0"))),
            np("f2", sub(sv("x2"), sv("x1"))),
            np("f3p", sub(sub(sv("x0"), sv("x2")), pv("t"))),
        ],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 0,
        },
        base_point: vec![
            ("x0".into(), vec![cz(0)]),
            ("x1".into(), vec![cz(0)]),
            ("x2".into(), vec![cz(0)]),
        ],
        ambient_lift: None,
        relative_reading: None,
        declaration_cover: None,
        affine_allowed: None,
        redundant_comparison: None,
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E8]),
    })
    .unwrap();
    let out_b = solve_lift_task(&task_b);
    assert_eq!(out_b.verdict, Verdict::Refuted);
    let db = out_b.lift.unwrap();
    assert_eq!(db.h0_dim, 1);
    assert_eq!(db.h1_dim, 1);
    assert!(!db.obstruction_is_zero);
    assert!(!db.lift_exists);
    let raw_b = db.raw_cech_comparison.unwrap();
    assert_eq!(raw_b.h1_t_raw_dim, 1);
    assert_eq!(raw_b.h1_d_dim, 1);
    assert!(raw_b.kernel_map_exact_verified && !raw_b.differs_from_full_syzygy);
}

#[test]
fn lift_h4_and_h10_relative_cone_two_context_cech_and_finish_snap_recovery() {
    // H10: variables = [delta, mu, E], laws = [E = 0, E - mu*delta = 0], obs = [delta, mu]
    // R' = Q[eps]/(eps^3) -> R = Q[eps]/(eps^2), base (eps, eps, 0), obs lift (eps, eps)
    let task_h10 = validate_lift_task(LiftTaskSpec {
        name: "h10_snapshot_obstruction".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["delta".into(), "mu".into(), "E".into()],
        ring_params: vec![],
        laws: vec![
            np("busy_zero", sv("E")),
            np("def_E", sub(sv("E"), mul(sv("mu"), sv("delta")))),
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
            ("delta".into(), vec![cz(0), cz(1), cz(0)]),
            ("mu".into(), vec![cz(0), cz(1), cz(0)]),
            ("E".into(), vec![cz(0), cz(0), cz(0)]),
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
                label: "raw_read_diff".into(),
                expr: PolyExpr::Neg(Box::new(mul(sv("mu"), sv("delta")))),
                negated: true,
            }),
        }),
        declaration_cover: Some(DeclarationCoverSpec {
            contexts: vec![
                DeclarationContextSpec {
                    name: "busy_law".into(),
                    vars: vec!["delta".into(), "mu".into(), "E".into()],
                    laws: vec!["busy_zero".into()],
                    observations: vec![np("read_E", sv("E"))],
                },
                DeclarationContextSpec {
                    name: "def_aux".into(),
                    vars: vec!["delta".into(), "mu".into(), "E".into()],
                    laws: vec!["def_E".into()],
                    observations: vec![np("read_prod", mul(sv("mu"), sv("delta")))],
                },
            ],
            two_context_cech: Some(TwoContextCechSpec {
                left_context: "busy_law".into(),
                right_context: "def_aux".into(),
                shared_vars: vec!["E".into()],
            }),
        }),
        affine_allowed: None,
        redundant_comparison: None,
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E5, MathClause::G141F5]),
    })
    .unwrap();

    let out_h10 = solve_lift_task(&task_h10);
    assert_eq!(out_h10.verdict, Verdict::Refuted);
    let d10 = out_h10.lift.unwrap();
    let rc10 = d10.relative_cone.unwrap();
    assert!(!rc10.relative_lift_exists);
    assert!(!rc10.relative_obstruction_is_zero);
    assert_eq!(rc10.raw_read_diff_value.as_deref(), Some("-eps^2"));
    assert_eq!(rc10.raw_read_diff_signed_match, Some(true));
    let cov10 = d10.declaration_cover.unwrap();
    assert!(cov10.support_closed);
    assert_eq!(
        cov10
            .two_context_cech_diff
            .as_ref()
            .unwrap()
            .get("E")
            .unwrap(),
        "eps^2"
    );
    assert_eq!(cov10.matches_relative_obstruction, Some(true));

    // H10 finish_snap 修復（旧 Busy Law `E = 0` を除き `E - mu*delta = 0` のみ）:
    // 障害消滅し、復元 lift E = eps^2 が独立再評価検算に合格する
    let task_snap = validate_lift_task(LiftTaskSpec {
        name: "h10_finish_snap_recovered".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["delta".into(), "mu".into(), "E".into()],
        ring_params: vec![],
        laws: vec![np("def_E", sub(sv("E"), mul(sv("mu"), sv("delta"))))],
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
            ("E".into(), vec![cz(0), cz(0), cz(0)]),
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
                label: "snap_read_diff".into(),
                expr: cz(0),
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
    let out_snap = solve_lift_task(&task_snap);
    assert_eq!(out_snap.verdict, Verdict::Established);
    let rc_snap = out_snap.lift.unwrap().relative_cone.unwrap();
    assert!(rc_snap.relative_lift_exists);
    assert!(rc_snap.relative_obstruction_is_zero);
    assert_eq!(
        rc_snap.restored_relative_lift.unwrap().get("E").unwrap(),
        "eps^2"
    );
    assert!(rc_snap.reevaluation.unwrap().matched);
    assert_eq!(rc_snap.raw_read_diff_signed_match, Some(true));
}

#[test]
fn lift_e7_cover_support_closure_and_c9_w5_etale_descent() {
    // E7: T = X + Y で {X}/{Y} 被覆は支持不閉、合併被覆 {X, Y, T} は支持閉包
    let make_e7 = |merged: bool| {
        let contexts = if merged {
            vec![DeclarationContextSpec {
                name: "merged".into(),
                vars: vec!["X".into(), "Y".into(), "T".into()],
                laws: vec!["sum_law".into()],
                observations: vec![np("obs_T", add(sv("X"), sv("Y")))],
            }]
        } else {
            vec![
                DeclarationContextSpec {
                    name: "ctx_X".into(),
                    vars: vec!["X".into(), "T".into()],
                    laws: vec![],
                    observations: vec![np("obs_T", add(sv("X"), sv("Y")))],
                },
                DeclarationContextSpec {
                    name: "ctx_Y".into(),
                    vars: vec!["Y".into()],
                    laws: vec![],
                    observations: vec![np("obs_Y", sv("Y"))],
                },
            ]
        };
        validate_lift_task(LiftTaskSpec {
            name: if merged { "e7_merged" } else { "e7_split" }.into(),
            coeff_domain: CoeffDomain::Q,
            variables: vec!["X".into(), "Y".into(), "T".into()],
            ring_params: vec![],
            laws: vec![np("sum_law", sub(sv("T"), add(sv("X"), sv("Y"))))],
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
                contexts,
                two_context_cech: None,
            }),
            affine_allowed: None,
            redundant_comparison: None,
            etale_descent: None,
            max_syzygy_pairs: None,
            provenance: prov(vec![MathClause::G141E7]),
        })
        .unwrap()
    };

    let split_cov = solve_lift_task(&make_e7(false))
        .lift
        .unwrap()
        .declaration_cover
        .unwrap();
    assert!(!split_cov.support_closed);
    assert!(split_cov.unclosed_observations.len() >= 2);
    assert!(
        split_cov
            .unclosed_observations
            .iter()
            .any(|s| s.contains("uncovered_law:sum_law"))
    );

    let merged_cov = solve_lift_task(&make_e7(true))
        .lift
        .unwrap()
        .declaration_cover
        .unwrap();
    assert!(merged_cov.support_closed);
    assert!(merged_cov.unclosed_observations.is_empty());

    // C9 / W5: パラメトリック d = 2, 3, 5 over Q および d = 2 over F_2（非 étale）
    for deg in [2u32, 3, 5] {
        let task = validate_lift_task(LiftTaskSpec {
            name: format!("c9_etale_d{deg}"),
            coeff_domain: CoeffDomain::Q,
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
                degree: deg,
                base_invertible: true,
            }),
            max_syzygy_pairs: None,
            provenance: prov(vec![MathClause::G141C9]),
        })
        .unwrap();
        let out = solve_lift_task(&task);
        assert_eq!(out.verdict, Verdict::Refuted);
        let et = out.lift.unwrap().etale_descent.unwrap();
        assert!(et.is_finite_etale && et.derivative_unit_verified && et.cocycle_verified);
        assert!(et.local_selection_exists_on_cover);
        assert!(!et.global_regular_section_exists);
        assert_eq!(et.cocycle_group, format!("mu_{deg}"));
    }

    // F_2 で d = 2 は導関数 2z = 0 のため非 étale => C9 適用条件不成立で沈黙する
    let task_insep = validate_lift_task(LiftTaskSpec {
        name: "c9_inseparable_f2".into(),
        coeff_domain: CoeffDomain::Fp(BigUint::from(2u32)),
        variables: vec!["t".into()],
        ring_params: vec![],
        laws: vec![],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 0,
        },
        base_point: vec![("t".into(), vec![cfp(1, 2)])],
        ambient_lift: None,
        relative_reading: None,
        declaration_cover: None,
        affine_allowed: None,
        redundant_comparison: None,
        etale_descent: Some(FiniteEtaleDescentSpec {
            base_var: "t".into(),
            cover_var: "z".into(),
            degree: 2,
            base_invertible: true,
        }),
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141C9]),
    })
    .unwrap();
    let out_f2 = solve_lift_task(&task_insep);
    assert!(matches!(
        out_f2.verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { .. })
    ));
}

#[test]
fn lift_silences_fail_closed_on_m2_nonzero_unobserved_z_nonlinear_and_pair_limit() {
    // 1. M^2 != 0 (Q[eps]/(eps^3) -> Q) => SquareZeroConditionViolated
    let bad_ext = validate_lift_task(LiftTaskSpec {
        name: "m2_nonzero".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["x".into()],
        ring_params: vec![],
        laws: vec![np("x2", pow(sv("x"), 2))],
        extension: SquareZeroSpec::ExplicitTable {
            r_prime_basis: vec!["1".into(), "e".into(), "e^2".into()],
            r_prime_one: vec![
                ScalarLit::Z(BigInt::from(1)),
                ScalarLit::Z(BigInt::from(0)),
                ScalarLit::Z(BigInt::from(0)),
            ],
            r_prime_mul: vec![
                vec![
                    vec![
                        ScalarLit::Z(1.into()),
                        ScalarLit::Z(0.into()),
                        ScalarLit::Z(0.into()),
                    ],
                    vec![
                        ScalarLit::Z(0.into()),
                        ScalarLit::Z(1.into()),
                        ScalarLit::Z(0.into()),
                    ],
                    vec![
                        ScalarLit::Z(0.into()),
                        ScalarLit::Z(0.into()),
                        ScalarLit::Z(1.into()),
                    ],
                ],
                vec![
                    vec![
                        ScalarLit::Z(0.into()),
                        ScalarLit::Z(1.into()),
                        ScalarLit::Z(0.into()),
                    ],
                    vec![
                        ScalarLit::Z(0.into()),
                        ScalarLit::Z(0.into()),
                        ScalarLit::Z(1.into()),
                    ],
                    vec![
                        ScalarLit::Z(0.into()),
                        ScalarLit::Z(0.into()),
                        ScalarLit::Z(0.into()),
                    ],
                ],
                vec![
                    vec![
                        ScalarLit::Z(0.into()),
                        ScalarLit::Z(0.into()),
                        ScalarLit::Z(1.into()),
                    ],
                    vec![
                        ScalarLit::Z(0.into()),
                        ScalarLit::Z(0.into()),
                        ScalarLit::Z(0.into()),
                    ],
                    vec![
                        ScalarLit::Z(0.into()),
                        ScalarLit::Z(0.into()),
                        ScalarLit::Z(0.into()),
                    ],
                ],
            ],
            r_base_basis: vec!["1".into()],
            r_base_one: vec![ScalarLit::Z(BigInt::from(1))],
            r_base_mul: vec![vec![vec![ScalarLit::Z(BigInt::from(1))]]],
            projection: vec![vec![
                ScalarLit::Z(BigInt::from(1)),
                ScalarLit::Z(BigInt::from(0)),
                ScalarLit::Z(BigInt::from(0)),
            ]],
        },
        base_point: vec![("x".into(), vec![cz(0)])],
        ambient_lift: None,
        relative_reading: None,
        declaration_cover: None,
        affine_allowed: None,
        redundant_comparison: None,
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E1]),
    })
    .unwrap();
    assert!(matches!(
        solve_lift_task(&bad_ext).verdict,
        Verdict::Undetermined(SilenceReason::SquareZeroConditionViolated { .. })
    ));

    // 2. 未観測依存 => UnobservedDependency
    let unobs = validate_lift_task(LiftTaskSpec {
        name: "unobs_lift".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["x".into()],
        ring_params: vec![],
        laws: vec![np("x_zero", sv("x"))],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 0,
        },
        base_point: vec![(
            "x".into(),
            vec![PolyExpr::Unobserved {
                slot: "missing_x".into(),
                origin: None,
            }],
        )],
        ambient_lift: None,
        relative_reading: None,
        declaration_cover: None,
        affine_allowed: None,
        redundant_comparison: None,
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E1]),
    })
    .unwrap();
    assert!(matches!(
        solve_lift_task(&unobs).verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { .. })
    ));

    // 3. Z 上未保証非線形 syzygy => SyzygyOutOfScope
    let z_nonlin = validate_lift_task(LiftTaskSpec {
        name: "z_nonlin_syz".into(),
        coeff_domain: CoeffDomain::Z,
        variables: vec!["x".into(), "y".into()],
        ring_params: vec![],
        laws: vec![
            np("f1", add(pow(sv("x"), 2), sv("y"))),
            np("f2", add(pow(sv("y"), 2), sv("x"))),
        ],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 0,
        },
        base_point: vec![("x".into(), vec![cz(0)]), ("y".into(), vec![cz(0)])],
        ambient_lift: None,
        relative_reading: None,
        declaration_cover: None,
        affine_allowed: None,
        redundant_comparison: None,
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: prov(vec![MathClause::G141E2]),
    })
    .unwrap();
    assert!(matches!(
        solve_lift_task(&z_nonlin).verdict,
        Verdict::Undetermined(SilenceReason::SyzygyOutOfScope { .. })
    ));

    // 4. syzygy 対上限超過 => SyzygyOutOfScope
    let pair_lim = validate_lift_task(LiftTaskSpec {
        name: "syz_pair_limit".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["x".into(), "y".into()],
        ring_params: vec![],
        laws: vec![np("f1", pow(sv("x"), 2)), np("f2", mul(sv("x"), sv("y")))],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 0,
        },
        base_point: vec![("x".into(), vec![cz(0)]), ("y".into(), vec![cz(0)])],
        ambient_lift: None,
        relative_reading: None,
        declaration_cover: None,
        affine_allowed: None,
        redundant_comparison: None,
        etale_descent: None,
        max_syzygy_pairs: Some(0),
        provenance: prov(vec![MathClause::G141E2]),
    })
    .unwrap();
    assert!(matches!(
        solve_lift_task(&pair_lim).verdict,
        Verdict::Undetermined(SilenceReason::SyzygyOutOfScope { .. })
    ));
}

#[test]
fn ideal_membership_and_relative_cone_with_nonempty_obs_laws() {
    use crate::algebra::{
        DEFAULT_MAX_SYZYGY_PAIRS, ExprBindings, MonomialOrder, Poly, ideal_membership_field,
    };

    // y ∈ <x*y + y, x> は単一 syzygy 生成元の定数 s[0] 検査では取りこぼしうる代表例。
    let (vars, bindings) =
        ExprBindings::from_slices(&["x".to_owned(), "y".to_owned()], &[], &[]).unwrap();
    let f1 = Poly::from_expr_q(&add(mul(sv("x"), sv("y")), sv("y")), &bindings).unwrap();
    let f2 = Poly::from_expr_q(&sv("x"), &bindings).unwrap();
    let target = Poly::from_expr_q(&sv("y"), &bindings).unwrap();
    let cofactors = ideal_membership_field(
        &target,
        &[f1.clone(), f2.clone()],
        &vars,
        MonomialOrder::Grevlex,
        DEFAULT_MAX_SYZYGY_PAIRS,
    )
    .unwrap()
    .expect("y lies in <x*y + y, x>");
    assert_eq!(cofactors[0].mul(&f1).add(&cofactors[1].mul(&f2)), target);

    // obs_laws = [w], reading_map = {w -> y}, laws = [x*y + y, x] の相対 cone 計算
    let task = validate_lift_task(LiftTaskSpec {
        name: "rel_cone_nonempty_obs_laws".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["x".into(), "y".into()],
        ring_params: vec![],
        laws: vec![
            np("l1", add(mul(sv("x"), sv("y")), sv("y"))),
            np("l2", sv("x")),
        ],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 0,
        },
        base_point: vec![("x".into(), vec![cz(0)]), ("y".into(), vec![cz(0)])],
        ambient_lift: Some(vec![
            ("x".into(), vec![cz(0), cz(0)]),
            ("y".into(), vec![cz(0), cz(0)]),
        ]),
        relative_reading: Some(RelativeReadingSpec {
            obs_vars: vec!["w".into()],
            obs_laws: vec![np("ol1", sv("w"))],
            reading_map: vec![("w".into(), sv("y"))],
            designated_obs_lift: vec![("w".into(), vec![cz(0), cz(0)])],
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

#[test]
fn two_context_cech_coboundary_vanishes_under_nonunique_local_lifts() {
    // s が両文脈で自由（K_L, K_R ともに s 成分非零）のとき、局所持ち上げに任意性があっても
    // Čech コバウンダリ類は 0 として貼り合わせ可能と判定される。
    let task = validate_lift_task(LiftTaskSpec {
        name: "cech_nonunique_coboundary".into(),
        coeff_domain: CoeffDomain::Q,
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
            ("a".into(), vec![cz(0), cz(1)]),
            ("b".into(), vec![cz(0), cz(2)]),
        ]),
        relative_reading: None,
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
        provenance: prov(vec![MathClause::G141E7]),
    })
    .unwrap();
    let out = solve_lift_task(&task);
    assert_eq!(out.verdict, Verdict::Established);
    let cov = out
        .lift
        .as_ref()
        .unwrap()
        .declaration_cover
        .as_ref()
        .unwrap();
    assert!(cov.support_closed);
    let diff = cov.two_context_cech_diff.as_ref().unwrap();
    assert_eq!(diff.get("s").map(String::as_str), Some("0"));
}
