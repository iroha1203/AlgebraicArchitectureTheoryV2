//! `solver/atlas*` の単体・パラメトリックテスト（G-141 G1–G5・H8・H12 / G-142 E–F・W3 / AC6・AC7）。

use crate::ir::atlas::{
    AtlasEvalConditionSpec, AtlasRefinementSpec, AtlasTaskSpec, AtomicOpCompareSpec,
    ExtendedLanguageCheckSpec, ExtendedOperationCheckSpec, ForgetfulReadingSpec, GraphEdgeSpec,
    validate_atlas_task,
};
use crate::ir::change::NamedPoly;
use crate::ir::diagnostics::{
    ChartSupportSpec, NerveEdgeSpec, NerveFaceSpec, SupportedNerveSpec,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::solver::solve_atlas_task;
use num_bigint::BigUint;

fn prov() -> Provenance {
    Provenance::new(
        vec![SourceRef::new("test_atlas", OriginKind::HumanAdopted)],
        vec![MathClause::G141G1, MathClause::G142E1],
    )
}

fn c_lit(dom: &CoeffDomain, n: i64) -> PolyExpr {
    match dom {
        CoeffDomain::Z => PolyExpr::Const(ScalarLit::int(n)),
        CoeffDomain::Q => PolyExpr::Const(ScalarLit::rat(n, 1).unwrap()),
        CoeffDomain::Fp(p) => PolyExpr::Const(ScalarLit::fp(n.into(), p.clone()).unwrap()),
    }
}

fn triangle_edges(dom: &CoeffDomain, b01: i64, b12: i64, b20: i64) -> Vec<GraphEdgeSpec> {
    vec![
        GraphEdgeSpec {
            name: "e01".into(),
            from: "v0".into(),
            to: "v1".into(),
            offset: c_lit(dom, b01),
        },
        GraphEdgeSpec {
            name: "e12".into(),
            from: "v1".into(),
            to: "v2".into(),
            offset: c_lit(dom, b12),
        },
        GraphEdgeSpec {
            name: "e20".into(),
            from: "v2".into(),
            to: "v0".into(),
            offset: c_lit(dom, b20),
        },
    ]
}

fn w3_refinement(dom: &CoeffDomain, b01: i64, b12: i64, b20: i64) -> AtlasRefinementSpec {
    AtlasRefinementSpec {
        fine_vertices: vec!["v0a".into(), "v0b".into(), "v1".into(), "v2".into()],
        fine_edges: vec![
            GraphEdgeSpec {
                name: "t".into(),
                from: "v0a".into(),
                to: "v0b".into(),
                offset: c_lit(dom, 0),
            },
            GraphEdgeSpec {
                name: "e01".into(),
                from: "v0b".into(),
                to: "v1".into(),
                offset: c_lit(dom, b01),
            },
            GraphEdgeSpec {
                name: "e12".into(),
                from: "v1".into(),
                to: "v2".into(),
                offset: c_lit(dom, b12),
            },
            GraphEdgeSpec {
                name: "e20".into(),
                from: "v2".into(),
                to: "v0a".into(),
                offset: c_lit(dom, b20),
            },
        ],
        vertex_map: vec![
            ("v0a".into(), "v0".into()),
            ("v0b".into(), "v0".into()),
            ("v1".into(), "v1".into()),
            ("v2".into(), "v2".into()),
        ],
        edge_map: vec![
            ("t".into(), None),
            ("e01".into(), Some("e01".into())),
            ("e12".into(), Some("e12".into())),
            ("e20".into(), Some("e20".into())),
        ],
        common_sources: vec!["s20".into(), "t".into(), "s01".into(), "s12".into()],
        coarse_reading: vec![
            ("s20".into(), "s20".into()),
            ("t".into(), "s01".into()),
            ("s01".into(), "s01".into()),
            ("s12".into(), "s12".into()),
        ],
        fine_reading: vec![
            ("s20".into(), "s20".into()),
            ("t".into(), "t".into()),
            ("s01".into(), "s01".into()),
            ("s12".into(), "s12".into()),
        ],
        coarse_nerve: SupportedNerveSpec {
            charts: vec![
                ChartSupportSpec {
                    name: "v0".into(),
                    support: vec!["s20".into(), "s01".into()],
                },
                ChartSupportSpec {
                    name: "v1".into(),
                    support: vec!["s01".into(), "s12".into()],
                },
                ChartSupportSpec {
                    name: "v2".into(),
                    support: vec!["s12".into(), "s20".into()],
                },
            ],
            edges: vec![
                NerveEdgeSpec {
                    name: "e01".into(),
                    left: "v0".into(),
                    right: "v1".into(),
                },
                NerveEdgeSpec {
                    name: "e12".into(),
                    left: "v1".into(),
                    right: "v2".into(),
                },
                NerveEdgeSpec {
                    name: "e20".into(),
                    left: "v2".into(),
                    right: "v0".into(),
                },
            ],
            faces: Vec::new(),
        },
        fine_nerve: SupportedNerveSpec {
            charts: vec![
                ChartSupportSpec {
                    name: "v0a".into(),
                    support: vec!["s20".into(), "t".into()],
                },
                ChartSupportSpec {
                    name: "v0b".into(),
                    support: vec!["t".into(), "s01".into()],
                },
                ChartSupportSpec {
                    name: "v1".into(),
                    support: vec!["s01".into(), "s12".into()],
                },
                ChartSupportSpec {
                    name: "v2".into(),
                    support: vec!["s12".into(), "s20".into()],
                },
            ],
            edges: vec![
                NerveEdgeSpec {
                    name: "t".into(),
                    left: "v0a".into(),
                    right: "v0b".into(),
                },
                NerveEdgeSpec {
                    name: "e01".into(),
                    left: "v0b".into(),
                    right: "v1".into(),
                },
                NerveEdgeSpec {
                    name: "e12".into(),
                    left: "v1".into(),
                    right: "v2".into(),
                },
                NerveEdgeSpec {
                    name: "e20".into(),
                    left: "v2".into(),
                    right: "v0a".into(),
                },
            ],
            faces: Vec::new(),
        },
        nerve_chart_map: vec![
            ("v0a".into(), "v0".into()),
            ("v0b".into(), "v0".into()),
            ("v1".into(), "v1".into()),
            ("v2".into(), "v2".into()),
        ],
        nerve_edge_map: vec![
            ("t".into(), None),
            ("e01".into(), Some("e01".into())),
            ("e12".into(), Some("e12".into())),
            ("e20".into(), Some("e20".into())),
        ],
        nerve_face_map: Vec::new(),
        eval_condition: None,
        forgetful_reading: None,
    }
}

#[test]
fn h8_w3_triangle_solvable_and_vertex_constraints_over_z_q_fp() {
    for dom in [
        CoeffDomain::Z,
        CoeffDomain::Q,
        CoeffDomain::Fp(BigUint::from(5u32)),
    ] {
        // 1. 全頂点許可: 1 自由度 torsor
        let task_all = validate_atlas_task(AtlasTaskSpec {
            name: format!("h8_all_{dom}"),
            coeff_domain: dom.clone(),
            vertices: vec!["v0".into(), "v1".into(), "v2".into()],
            edges: triangle_edges(&dom, 1, 2, -3),
            mu: c_lit(&dom, 1),
            base_lambdas: vec![
                ("v0".into(), c_lit(&dom, 0)),
                ("v1".into(), c_lit(&dom, 0)),
                ("v2".into(), c_lit(&dom, 0)),
            ],
            allowed_vertices: vec!["v0".into(), "v1".into(), "v2".into()],
            allowed_edges: Vec::new(),
            compare_to_q: matches!(dom, CoeffDomain::Z),
            refinement: None,
            extended_language_check: None,
            provenance: prov(),
        })
        .unwrap();
        let out = solve_atlas_task(&task_all);
        assert_eq!(out.verdict, Verdict::Established);
        let a = out.atlas.as_ref().unwrap();
        assert!(a.graph_connected);
        assert!(a.saga_sign_commutes_verified);
        assert!(a.primitive_relation_connected_verified);
        assert_eq!(a.diagnostic_h1_rank, 1);
        assert!(a.o_b_is_zero);
        assert!(a.kappa_b_is_zero);
        assert!(a.unconstrained_global_operation_exists);
        assert_eq!(a.unconstrained_h0_torsor_rank, 1);
        assert!(a.unconstrained_reevaluation.as_ref().unwrap().matched);
        if matches!(dom, CoeffDomain::Z) {
            assert_eq!(a.z_to_q_zero_reflection_verified, Some(true));
        }
        assert!(a.vertex_constrained_repair.repair_exists);
        assert_eq!(a.vertex_constrained_repair.torsor_basis.len(), 1);
        assert!(a.vertex_constrained_repair.reevaluation.as_ref().unwrap().matched);

        // 2. 1 頂点固定 (v0 固定): 一意解 (0, 1, 3)
        let task_fix1 = validate_atlas_task(AtlasTaskSpec {
            name: format!("h8_fix1_{dom}"),
            coeff_domain: dom.clone(),
            vertices: vec!["v0".into(), "v1".into(), "v2".into()],
            edges: triangle_edges(&dom, 1, 2, -3),
            mu: c_lit(&dom, 1),
            base_lambdas: vec![
                ("v0".into(), c_lit(&dom, 0)),
                ("v1".into(), c_lit(&dom, 0)),
                ("v2".into(), c_lit(&dom, 0)),
            ],
            allowed_vertices: vec!["v1".into(), "v2".into()],
            allowed_edges: Vec::new(),
            compare_to_q: false,
            refinement: None,
            extended_language_check: None,
            provenance: prov(),
        })
        .unwrap();
        let a1 = solve_atlas_task(&task_fix1).atlas.unwrap();
        assert!(a1.vertex_constrained_repair.repair_exists);
        assert_eq!(a1.vertex_constrained_repair.torsor_basis.len(), 0);
        let pd = a1.vertex_constrained_repair.particular_delta.as_ref().unwrap();
        assert_eq!(pd["v0"], "0");
        assert_eq!(pd["v1"], "1");
        assert_eq!(pd["v2"], "3");
        assert!(a1.vertex_constrained_repair.reevaluation.as_ref().unwrap().matched);

        // 3. W3 対照: 無制約 κ_b = 0 かつ全頂点固定 -> 制約付き修復不能
        let task_fix_all = validate_atlas_task(AtlasTaskSpec {
            name: format!("w3_fix_all_{dom}"),
            coeff_domain: dom.clone(),
            vertices: vec!["v0".into(), "v1".into(), "v2".into()],
            edges: triangle_edges(&dom, 1, 2, -3),
            mu: c_lit(&dom, 1),
            base_lambdas: vec![
                ("v0".into(), c_lit(&dom, 0)),
                ("v1".into(), c_lit(&dom, 0)),
                ("v2".into(), c_lit(&dom, 0)),
            ],
            allowed_vertices: Vec::new(),
            allowed_edges: Vec::new(),
            compare_to_q: false,
            refinement: None,
            extended_language_check: None,
            provenance: prov(),
        })
        .unwrap();
        let af = solve_atlas_task(&task_fix_all).atlas.unwrap();
        assert!(af.o_b_is_zero);
        assert!(af.kappa_b_is_zero);
        assert!(!af.vertex_constrained_repair.repair_exists);
    }
}

#[test]
fn h8_w3_triangle_obstructed_and_edge_repairs() {
    let dom = CoeffDomain::Q;
    // b = (1, 0, 0): 全辺許可 -> 2 次元平面、1 辺許可 -> 単点 -1、0 辺許可 -> 空
    for (allowed_e, exp_exists, exp_torsor_rank, exp_h0) in [
        (vec!["e01".into(), "e12".into(), "e20".into()], true, 2, 1),
        (vec!["e01".into()], true, 0, 1),
        (Vec::new(), false, 0, 0),
    ] {
        let task = validate_atlas_task(AtlasTaskSpec {
            name: "h8_obstructed".into(),
            coeff_domain: dom.clone(),
            vertices: vec!["v0".into(), "v1".into(), "v2".into()],
            edges: triangle_edges(&dom, 1, 0, 0),
            mu: c_lit(&dom, 1),
            base_lambdas: vec![
                ("v0".into(), c_lit(&dom, 0)),
                ("v1".into(), c_lit(&dom, 0)),
                ("v2".into(), c_lit(&dom, 0)),
            ],
            allowed_vertices: vec!["v0".into(), "v1".into(), "v2".into()],
            allowed_edges: allowed_e,
            compare_to_q: false,
            refinement: None,
            extended_language_check: None,
            provenance: prov(),
        })
        .unwrap();
        let out = solve_atlas_task(&task);
        assert_eq!(out.verdict, Verdict::Refuted);
        let a = out.atlas.unwrap();
        assert!(!a.o_b_is_zero);
        assert!(!a.kappa_b_is_zero);
        assert_eq!(a.diagnostic_h1_rank, 1); // offset に依存せず一定！
        assert!(!a.unconstrained_global_operation_exists);
        assert_eq!(a.edge_constrained_repair.repair_exists, exp_exists);
        assert_eq!(a.edge_constrained_repair.torsor_basis.len(), exp_torsor_rank);
        assert_eq!(a.edge_constrained_repair.h0_operation_torsor_rank, exp_h0);
        if exp_exists {
            assert!(a.edge_constrained_repair.reevaluation.as_ref().unwrap().matched);
            if exp_torsor_rank == 0 {
                let pd = a.edge_constrained_repair.particular_delta.as_ref().unwrap();
                assert_eq!(pd["e01"], "-1");
            }
        }
    }

    // Z 上の b = (1, 0, 0) で Z -> Q 零性反映検算
    let task_z = validate_atlas_task(AtlasTaskSpec {
        name: "h8_obstructed_z".into(),
        coeff_domain: CoeffDomain::Z,
        vertices: vec!["v0".into(), "v1".into(), "v2".into()],
        edges: triangle_edges(&CoeffDomain::Z, 1, 0, 0),
        mu: c_lit(&CoeffDomain::Z, 1),
        base_lambdas: vec![
            ("v0".into(), c_lit(&CoeffDomain::Z, 0)),
            ("v1".into(), c_lit(&CoeffDomain::Z, 0)),
            ("v2".into(), c_lit(&CoeffDomain::Z, 0)),
        ],
        allowed_vertices: Vec::new(),
        allowed_edges: vec!["e01".into()],
        compare_to_q: true,
        refinement: None,
        extended_language_check: None,
        provenance: prov(),
    })
    .unwrap();
    let az = solve_atlas_task(&task_z).atlas.unwrap();
    assert!(!az.o_b_is_zero);
    assert_eq!(az.z_to_q_zero_reflection_verified, Some(true));
    assert!(az.edge_constrained_repair.repair_exists);
    assert!(az.edge_constrained_repair.reevaluation.as_ref().unwrap().matched);
}

#[test]
fn w3_eight_point_refinement_c0_to_c6_eval_condition_and_f7() {
    for dom in [CoeffDomain::Z, CoeffDomain::Q] {
        let mut r = w3_refinement(&dom, 1, 2, -3);
        r.eval_condition = Some(AtlasEvalConditionSpec {
            evaluations: vec![NamedPoly {
                name: "eval_v1".into(),
                expr: PolyExpr::StateVar("v1".into()),
                provenance: None,
            }],
            equations: vec![NamedPoly {
                name: "fix_v0".into(),
                expr: PolyExpr::StateVar("v0".into()),
                provenance: None,
            }],
            invertibles: vec![NamedPoly {
                name: "v1_nonzero".into(),
                expr: PolyExpr::StateVar("v1".into()),
                provenance: None,
            }],
        });
        r.forgetful_reading = Some(ForgetfulReadingSpec {
            forgotten_var: "t".into(),
            eval_expr: PolyExpr::StateVar("t".into()),
            condition_eq: PolyExpr::Sub(
                Box::new(PolyExpr::StateVar("t".into())),
                Box::new(c_lit(&dom, 1)),
            ),
            sample_values: vec![c_lit(&dom, 0), c_lit(&dom, 1)],
        });

        let task = validate_atlas_task(AtlasTaskSpec {
            name: format!("w3_ref_{dom}"),
            coeff_domain: dom.clone(),
            vertices: vec!["v0".into(), "v1".into(), "v2".into()],
            edges: triangle_edges(&dom, 1, 2, -3),
            mu: c_lit(&dom, 1),
            base_lambdas: vec![
                ("v0".into(), c_lit(&dom, 0)),
                ("v1".into(), c_lit(&dom, 0)),
                ("v2".into(), c_lit(&dom, 0)),
            ],
            allowed_vertices: vec!["v0".into(), "v1".into(), "v2".into()],
            allowed_edges: Vec::new(),
            compare_to_q: matches!(dom, CoeffDomain::Z),
            refinement: Some(r),
            extended_language_check: None,
            provenance: prov(),
        })
        .unwrap();

        let out = solve_atlas_task(&task);
        assert_eq!(out.verdict, Verdict::Established);
        let ref_res = out.atlas.unwrap().refinement.unwrap();
        assert!(ref_res.condition_c.all_passed);
        assert!(ref_res.condition_c.c0_support_image);
        assert!(ref_res.condition_c.c1_block_fiber_connected);
        assert!(ref_res.condition_c.c2_edge_lift);
        assert!(ref_res.condition_c.c3_fiber_rational_1_cycles);
        assert!(ref_res.condition_c.c4_face_lift);
        assert!(ref_res.condition_c.c5_edge_lift_unique);
        assert!(ref_res.condition_c.c6_self_loop);
        assert!(ref_res.cochain_map_commutes);
        assert!(ref_res.h0_isomorphism);
        assert!(ref_res.h1_isomorphism);
        assert!(ref_res.designated_o_preserved);
        assert!(ref_res.designated_kappa_preserved);
        assert!(ref_res.repair_fiber_isomorphism_verified);
        assert!(ref_res.inverse_reconstruction_verified);
        assert_eq!(ref_res.eval_condition_fiber_preserved, Some(true));

        let fg = ref_res.forgetful_reading_contrast.unwrap();
        assert!(fg.adequacy_and_c0_c6_hold);
        assert!(!fg.eval_constant_on_fiber);
        assert!(!fg.eval_descends_to_coarse);
        assert!(!fg.condition_constant_on_fiber);
        assert!(!fg.condition_descends_to_coarse);
        assert_eq!(fg.sample_condition_holds.get("0"), Some(&false));
        assert_eq!(fg.sample_condition_holds.get("1"), Some(&true));
    }
}

#[test]
fn condition_c0_to_c6_each_fails_independently() {
    let dom = CoeffDomain::Q;
    let run_ref = |r: AtlasRefinementSpec| {
        let task = validate_atlas_task(AtlasTaskSpec {
            name: "cond_c_neg".into(),
            coeff_domain: dom.clone(),
            vertices: vec!["v0".into(), "v1".into(), "v2".into()],
            edges: triangle_edges(&dom, 1, 2, -3),
            mu: c_lit(&dom, 1),
            base_lambdas: vec![
                ("v0".into(), c_lit(&dom, 0)),
                ("v1".into(), c_lit(&dom, 0)),
                ("v2".into(), c_lit(&dom, 0)),
            ],
            allowed_vertices: vec!["v0".into(), "v1".into(), "v2".into()],
            allowed_edges: Vec::new(),
            compare_to_q: false,
            refinement: Some(r),
            extended_language_check: None,
            provenance: prov(),
        })
        .unwrap();
        solve_atlas_task(&task).atlas.unwrap().refinement.unwrap().condition_c
    };

    // C0 違反: fine v0b の支持から s01 を落とす -> v0 の像が {s20} != {s20, s01}
    let mut r_c0 = w3_refinement(&dom, 1, 2, -3);
    r_c0.fine_nerve.charts[1].support = vec!["t".into()];
    r_c0.coarse_reading = vec![
        ("s20".into(), "s20".into()),
        ("t".into(), "s20".into()),
        ("s01".into(), "s01".into()),
        ("s12".into(), "s12".into()),
    ];
    assert!(!run_ref(r_c0).c0_support_image);

    // C1 違反: 内部辺 t を fine_nerve から除去 -> v0 fiber {v0a, v0b} が非連結
    let mut r_c1 = w3_refinement(&dom, 1, 2, -3);
    r_c1.fine_nerve.edges.retain(|e| e.name != "t");
    r_c1.nerve_edge_map.retain(|(e, _)| e != "t");
    let c1 = run_ref(r_c1);
    assert!(c1.c0_support_image);
    assert!(!c1.c1_block_fiber_connected);

    // C2 違反（正当な TargetSupportedNerveMorphism 上で粗辺 e01 の細 lift を除去）
    let mut r_c2 = w3_refinement(&dom, 1, 2, -3);
    r_c2.fine_nerve.edges.retain(|e| e.name != "e01");
    r_c2.nerve_edge_map.retain(|(fe, _)| fe != "e01");
    assert!(!run_ref(r_c2).c2_edge_lift);

    // C3 違反: v0 fiber 内に 3 頂点 cycle を face なしで作る
    let mut r_c3 = w3_refinement(&dom, 1, 2, -3);
    r_c3.fine_nerve.charts.push(ChartSupportSpec {
        name: "v0c".into(),
        support: vec!["t".into()],
    });
    r_c3.nerve_chart_map.push(("v0c".into(), "v0".into()));
    r_c3.fine_nerve.edges.push(NerveEdgeSpec {
        name: "t_bc".into(),
        left: "v0b".into(),
        right: "v0c".into(),
    });
    r_c3.fine_nerve.edges.push(NerveEdgeSpec {
        name: "t_ca".into(),
        left: "v0c".into(),
        right: "v0a".into(),
    });
    r_c3.nerve_edge_map.push(("t_bc".into(), None));
    r_c3.nerve_edge_map.push(("t_ca".into(), None));
    let c3 = run_ref(r_c3.clone());
    assert!(c3.c1_block_fiber_connected);
    assert!(!c3.c3_fiber_rational_1_cycles);

    // C3 回復: 同じ 3 頂点 cycle を埋める内部 face を追加すると C3 が成立する
    let mut r_c3_filled = r_c3;
    r_c3_filled.fine_nerve.edges.retain(|e| e.name != "t_ca");
    r_c3_filled.nerve_edge_map.retain(|(e, _)| e != "t_ca");
    r_c3_filled.fine_nerve.edges.push(NerveEdgeSpec {
        name: "t_ac".into(),
        left: "v0a".into(),
        right: "v0c".into(),
    });
    r_c3_filled.nerve_edge_map.push(("t_ac".into(), None));
    r_c3_filled.fine_nerve.faces.push(NerveFaceSpec {
        name: "f_fiber".into(),
        e0: "t".into(),
        e1: "t_ac".into(),
        e2: "t_bc".into(),
    });
    r_c3_filled.nerve_face_map.push(("f_fiber".into(), None));
    assert!(run_ref(r_c3_filled).c3_fiber_rational_1_cycles);

    // C4 違反: 粗 nerve に非空 face を追加し fine に lift を置かない（辺向きも整合する正当な射）
    let mut r_c4 = w3_refinement(&dom, 1, 2, -3);
    r_c4.coarse_nerve.charts[0].support.push("s12".into());
    r_c4.coarse_nerve.edges = vec![
        NerveEdgeSpec {
            name: "e01".into(),
            left: "v0".into(),
            right: "v1".into(),
        },
        NerveEdgeSpec {
            name: "e02".into(),
            left: "v0".into(),
            right: "v2".into(),
        },
        NerveEdgeSpec {
            name: "e12".into(),
            left: "v1".into(),
            right: "v2".into(),
        },
    ];
    r_c4.coarse_nerve.faces = vec![NerveFaceSpec {
        name: "f012".into(),
        e0: "e01".into(),
        e1: "e02".into(),
        e2: "e12".into(),
    }];
    r_c4.fine_nerve.edges[3] = NerveEdgeSpec {
        name: "e20".into(),
        left: "v0a".into(),
        right: "v2".into(),
    };
    for (_, ce) in &mut r_c4.nerve_edge_map {
        if ce.as_deref() == Some("e20") {
            *ce = Some("e02".into());
        }
    }
    assert!(!run_ref(r_c4).c4_face_lift);

    // C5 違反（正当な TargetSupportedNerveMorphism 上で同一端点の 2 本の細辺を同じ粗辺 e01 へ写す）
    let mut r_c5 = w3_refinement(&dom, 1, 2, -3);
    r_c5.fine_nerve.edges.push(NerveEdgeSpec {
        name: "e01_dup".into(),
        left: "v0b".into(),
        right: "v1".into(),
    });
    r_c5.nerve_edge_map
        .push(("e01_dup".into(), Some("e01".into())));
    assert!(!run_ref(r_c5).c5_edge_lift_unique);

    // TargetSupportedNerveMorphism 射公理違反（異なる粗 chart 間を結ぶ細辺を None へ写像）は fail-closed 沈黙（Finding 1）
    let mut r_bad_morph = w3_refinement(&dom, 1, 2, -3);
    r_bad_morph.fine_nerve.edges.push(NerveEdgeSpec {
        name: "bad_cross".into(),
        left: "v0b".into(),
        right: "v2".into(),
    });
    r_bad_morph.nerve_edge_map.push(("bad_cross".into(), None));
    let bad_task = validate_atlas_task(AtlasTaskSpec {
        name: "bad_nerve_morph".into(),
        coeff_domain: dom.clone(),
        vertices: vec!["v0".into(), "v1".into(), "v2".into()],
        edges: triangle_edges(&dom, 1, 2, -3),
        mu: c_lit(&dom, 1),
        base_lambdas: vec![
            ("v0".into(), c_lit(&dom, 0)),
            ("v1".into(), c_lit(&dom, 0)),
            ("v2".into(), c_lit(&dom, 0)),
        ],
        allowed_vertices: vec!["v0".into(), "v1".into(), "v2".into()],
        allowed_edges: Vec::new(),
        compare_to_q: false,
        refinement: Some(r_bad_morph),
        extended_language_check: None,
        provenance: prov(),
    })
    .unwrap();
    assert!(matches!(
        solve_atlas_task(&bad_task).verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { ref condition, .. })
            if condition == "target_supported_nerve_morphism_axioms"
    ));

    // chartSupport_compatible 違反（fine v0a に粗 v0 支持外の s12 を混入）も fail-closed 沈黙（R2 Major）
    let mut r_bad_sup = w3_refinement(&dom, 1, 2, -3);
    r_bad_sup.fine_nerve.charts[0].support.push("s12".into());
    let bad_sup_task = validate_atlas_task(AtlasTaskSpec {
        name: "bad_chart_support".into(),
        coeff_domain: dom.clone(),
        vertices: vec!["v0".into(), "v1".into(), "v2".into()],
        edges: triangle_edges(&dom, 1, 2, -3),
        mu: c_lit(&dom, 1),
        base_lambdas: vec![
            ("v0".into(), c_lit(&dom, 0)),
            ("v1".into(), c_lit(&dom, 0)),
            ("v2".into(), c_lit(&dom, 0)),
        ],
        allowed_vertices: vec!["v0".into(), "v1".into(), "v2".into()],
        allowed_edges: Vec::new(),
        compare_to_q: false,
        refinement: Some(r_bad_sup),
        extended_language_check: None,
        provenance: prov(),
    })
    .unwrap();
    assert!(matches!(
        solve_atlas_task(&bad_sup_task).verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { ref condition, .. })
            if condition == "target_supported_nerve_morphism_axioms"
    ));

    // C6 違反: 粗 self-loop へ非 self-loop の細辺を写す
    let mut r_c6 = w3_refinement(&dom, 1, 2, -3);
    r_c6.coarse_nerve.edges.push(NerveEdgeSpec {
        name: "loop0".into(),
        left: "v0".into(),
        right: "v0".into(),
    });
    for (fe, ce) in &mut r_c6.nerve_edge_map {
        if fe == "t" {
            *ce = Some("loop0".into());
        }
    }
    assert!(!run_ref(r_c6).c6_self_loop);
}

#[test]
fn h12_atomic_ops_commute_but_extended_protocol_and_runtime_arg_fail() {
    let q = CoeffDomain::Q;
    let var = |s: &str| PolyExpr::StateVar(s.into());
    let arg = |s: &str| PolyExpr::ArgVar(s.into());
    let add = |a: PolyExpr, b: PolyExpr| PolyExpr::Add(Box::new(a), Box::new(b));
    let sub = |a: PolyExpr, b: PolyExpr| PolyExpr::Sub(Box::new(a), Box::new(b));
    let mul = |a: PolyExpr, b: PolyExpr| PolyExpr::Mul(Box::new(a), Box::new(b));

    // g_1(B, C) = (2B + C, -B)
    let ext = ExtendedLanguageCheckSpec {
        state_vars: vec!["B".into(), "C".into()],
        adapter_map: vec![
            ("B".into(), add(mul(c_lit(&q, 2), var("B")), var("C"))),
            ("C".into(), PolyExpr::Neg(Box::new(var("B")))),
        ],
        atomic_ops: vec![
            // apply_u: before (B + u, C), after (B + 2u, C - u)
            AtomicOpCompareSpec {
                name: "apply".into(),
                arg_vars: vec!["u".into()],
                before_updates: vec![("B".into(), add(var("B"), arg("u"))), ("C".into(), var("C"))],
                after_updates: vec![
                    ("B".into(), add(var("B"), mul(c_lit(&q, 2), arg("u")))),
                    ("C".into(), sub(var("C"), arg("u"))),
                ],
            },
            // compact_t: before (B + t, C - t), after (B + t, C - t)
            AtomicOpCompareSpec {
                name: "compact".into(),
                arg_vars: vec!["t".into()],
                before_updates: vec![
                    ("B".into(), add(var("B"), arg("t"))),
                    ("C".into(), sub(var("C"), arg("t"))),
                ],
                after_updates: vec![
                    ("B".into(), add(var("B"), arg("t"))),
                    ("C".into(), sub(var("C"), arg("t"))),
                ],
            },
        ],
        extended_checks: vec![
            // Snapshot protocol: (0,0,0) -> begin -> apply_1 -> finish
            ExtendedOperationCheckSpec::ProtocolSequence {
                name: "snapshot_protocol".into(),
                extended_state_vars: vec!["B".into(), "C".into(), "h".into()],
                initial_state: vec![
                    ("B".into(), c_lit(&q, 0)),
                    ("C".into(), c_lit(&q, 0)),
                    ("h".into(), c_lit(&q, 0)),
                ],
                before_steps: vec![
                    vec![("B".into(), var("B")), ("C".into(), var("C")), ("h".into(), var("C"))],
                    vec![
                        ("B".into(), add(var("B"), c_lit(&q, 1))),
                        ("C".into(), var("C")),
                        ("h".into(), var("h")),
                    ],
                    vec![
                        ("B".into(), add(var("B"), var("h"))),
                        ("C".into(), sub(var("C"), var("C"))),
                        ("h".into(), var("h")),
                    ],
                ],
                after_steps: vec![
                    vec![("B".into(), var("B")), ("C".into(), var("C")), ("h".into(), var("C"))],
                    vec![
                        ("B".into(), add(var("B"), c_lit(&q, 2))),
                        ("C".into(), sub(var("C"), c_lit(&q, 1))),
                        ("h".into(), var("h")),
                    ],
                    vec![
                        ("B".into(), add(var("B"), var("h"))),
                        ("C".into(), sub(var("C"), var("C"))),
                        ("h".into(), var("h")),
                    ],
                ],
                before_read: Box::new(add(var("B"), var("C"))),
                after_read: Box::new(add(var("B"), var("C"))),
                intermediate_laws: vec![NamedPoly {
                    name: "busy_law".into(),
                    expr: sub(var("h"), var("C")),
                    provenance: None,
                }],
            },
            // compact_all(B, C) = (B + C, 0) at (1, 0) and equalizer point (0, 0) (Finding 4)
            ExtendedOperationCheckSpec::RuntimeArgOp {
                name: "compact_all".into(),
                before_updates: vec![
                    ("B".into(), add(var("B"), var("C"))),
                    ("C".into(), c_lit(&q, 0)),
                ],
                after_updates: vec![
                    ("B".into(), add(var("B"), var("C"))),
                    ("C".into(), c_lit(&q, 0)),
                ],
                sample_state: vec![("B".into(), c_lit(&q, 1)), ("C".into(), c_lit(&q, 0))],
            },
            ExtendedOperationCheckSpec::RuntimeArgOp {
                name: "compact_all_at_equalizer".into(),
                before_updates: vec![
                    ("B".into(), add(var("B"), var("C"))),
                    ("C".into(), c_lit(&q, 0)),
                ],
                after_updates: vec![
                    ("B".into(), add(var("B"), var("C"))),
                    ("C".into(), c_lit(&q, 0)),
                ],
                sample_state: vec![("B".into(), c_lit(&q, 0)), ("C".into(), c_lit(&q, 0))],
            },
        ],
    };

    let task = validate_atlas_task(AtlasTaskSpec {
        name: "h12".into(),
        coeff_domain: q.clone(),
        vertices: vec!["v0".into(), "v1".into()],
        edges: vec![GraphEdgeSpec {
            name: "e01".into(),
            from: "v0".into(),
            to: "v1".into(),
            offset: c_lit(&q, 1),
        }],
        mu: c_lit(&q, 1),
        base_lambdas: vec![("v0".into(), c_lit(&q, 1)), ("v1".into(), c_lit(&q, 2))],
        allowed_vertices: Vec::new(),
        allowed_edges: Vec::new(),
        compare_to_q: false,
        refinement: None,
        extended_language_check: Some(ext),
        provenance: prov(),
    })
    .unwrap();

    let out = solve_atlas_task(&task);
    assert_eq!(out.verdict, Verdict::Refuted);
    let ext_res = out.atlas.unwrap().extended_language_non_transport.unwrap();
    assert!(ext_res.all_atomic_ops_commute);
    assert_eq!(ext_res.atomic_ops_commute.get("apply"), Some(&true));
    assert_eq!(ext_res.atomic_ops_commute.get("compact"), Some(&true));
    assert!(!ext_res.all_extended_checks_preserved);

    let proto = &ext_res.extended_check_results[0];
    assert_eq!(proto.kind, "protocol_sequence");
    assert!(!proto.transport_preserved);
    assert_eq!(proto.before_values, vec!["1"]);
    assert_eq!(proto.after_values, vec!["2"]);
    assert!(proto.law_residuals.iter().any(|r| r.contains("busy_law=1")));

    let rt = &ext_res.extended_check_results[1];
    assert_eq!(rt.kind, "runtime_arg_op");
    assert!(!rt.transport_preserved);
    assert_eq!(rt.before_values, vec!["2", "-1"]);
    assert_eq!(rt.after_values, vec!["1", "0"]);

    // 等化子点 (0, 0) でも多項式恒等式不一致により transport_preserved == false かつ多項式残差が出力される
    let rt_eq = &ext_res.extended_check_results[2];
    assert_eq!(rt_eq.kind, "runtime_arg_op");
    assert!(!rt_eq.transport_preserved);
    assert_eq!(rt_eq.before_values, vec!["0", "0"]);
    assert_eq!(rt_eq.after_values, vec!["0", "0"]);
    assert!(!rt_eq.law_residuals.is_empty());
}

#[test]
fn atlas_two_cycle_graph_and_silence_disconnected_or_unobserved() {
    // 1. 非三角形一般グラフ（4 頂点 5 辺 => |E|-|V|+1 = 2 の 2-chord グラフ）
    let q = CoeffDomain::Q;
    let task_2c = validate_atlas_task(AtlasTaskSpec {
        name: "two_cycles".into(),
        coeff_domain: q.clone(),
        vertices: vec!["v0".into(), "v1".into(), "v2".into(), "v3".into()],
        edges: vec![
            GraphEdgeSpec {
                name: "e01".into(),
                from: "v0".into(),
                to: "v1".into(),
                offset: c_lit(&q, 1),
            },
            GraphEdgeSpec {
                name: "e12".into(),
                from: "v1".into(),
                to: "v2".into(),
                offset: c_lit(&q, 2),
            },
            GraphEdgeSpec {
                name: "e20".into(),
                from: "v2".into(),
                to: "v0".into(),
                offset: c_lit(&q, -3),
            },
            GraphEdgeSpec {
                name: "e03".into(),
                from: "v0".into(),
                to: "v3".into(),
                offset: c_lit(&q, 4),
            },
            GraphEdgeSpec {
                name: "e32".into(),
                from: "v3".into(),
                to: "v2".into(),
                offset: c_lit(&q, -1),
            },
        ],
        mu: c_lit(&q, 1),
        base_lambdas: vec![
            ("v0".into(), c_lit(&q, 0)),
            ("v1".into(), c_lit(&q, 0)),
            ("v2".into(), c_lit(&q, 0)),
            ("v3".into(), c_lit(&q, 0)),
        ],
        allowed_vertices: vec!["v0".into(), "v1".into(), "v2".into(), "v3".into()],
        allowed_edges: vec!["e20".into(), "e32".into()],
        compare_to_q: false,
        refinement: None,
        extended_language_check: None,
        provenance: prov(),
    })
    .unwrap();
    let out_2c = solve_atlas_task(&task_2c);
    assert_eq!(out_2c.verdict, Verdict::Established);
    let a2c = out_2c.atlas.unwrap();
    assert_eq!(a2c.diagnostic_h1_rank, 2);
    assert_eq!(a2c.chord_edges.len(), 2);
    assert!(a2c.o_b_is_zero);
    assert!(a2c.saga_sign_commutes_verified);
    assert!(a2c.primitive_relation_connected_verified);
    assert!(a2c.unconstrained_reevaluation.as_ref().unwrap().matched);

    // 2. 非連結グラフ -> DisconnectedGraphOutOfScope 沈黙
    let task_disc = validate_atlas_task(AtlasTaskSpec {
        name: "disconnected".into(),
        coeff_domain: q.clone(),
        vertices: vec!["v0".into(), "v1".into(), "v2".into(), "v3".into()],
        edges: vec![
            GraphEdgeSpec {
                name: "e01".into(),
                from: "v0".into(),
                to: "v1".into(),
                offset: c_lit(&q, 0),
            },
            GraphEdgeSpec {
                name: "e23".into(),
                from: "v2".into(),
                to: "v3".into(),
                offset: c_lit(&q, 0),
            },
        ],
        mu: c_lit(&q, 1),
        base_lambdas: vec![
            ("v0".into(), c_lit(&q, 0)),
            ("v1".into(), c_lit(&q, 0)),
            ("v2".into(), c_lit(&q, 0)),
            ("v3".into(), c_lit(&q, 0)),
        ],
        allowed_vertices: Vec::new(),
        allowed_edges: Vec::new(),
        compare_to_q: false,
        refinement: None,
        extended_language_check: None,
        provenance: prov(),
    })
    .unwrap();
    assert!(matches!(
        solve_atlas_task(&task_disc).verdict,
        Verdict::Undetermined(SilenceReason::DisconnectedGraphOutOfScope { .. })
    ));

    // 3. 未観測 offset -> UnobservedDependency 沈黙
    let task_unobs = validate_atlas_task(AtlasTaskSpec {
        name: "unobs_atlas".into(),
        coeff_domain: q.clone(),
        vertices: vec!["v0".into(), "v1".into()],
        edges: vec![GraphEdgeSpec {
            name: "e01".into(),
            from: "v0".into(),
            to: "v1".into(),
            offset: PolyExpr::Unobserved {
                slot: "missing_b".into(),
                origin: Some(SourceRef::new("u", OriginKind::LlmCandidate)),
            },
        }],
        mu: c_lit(&q, 1),
        base_lambdas: vec![("v0".into(), c_lit(&q, 0)), ("v1".into(), c_lit(&q, 0))],
        allowed_vertices: Vec::new(),
        allowed_edges: Vec::new(),
        compare_to_q: false,
        refinement: None,
        extended_language_check: None,
        provenance: prov(),
    })
    .unwrap();
    assert!(matches!(
        solve_atlas_task(&task_unobs).verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { .. })
    ));
}
