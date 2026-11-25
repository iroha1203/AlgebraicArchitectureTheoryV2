//! `solver/diagnostics*` の単体・パラメトリックテスト（G-142 A–D・W1–W2 / AC5・AC7）。

use crate::ir::change::NamedPoly;
use crate::ir::diagnostics::{
    ChartSupportSpec, CoeffChangeComparisonSpec, CollisionComparisonSpec, DiagnosticsReadoutSpec,
    DiagnosticsTaskSpec, DimensionRealizationSpec, ExplicitZComplexSpec, NamedBasePointSpec,
    NamedRPointSpec, NerveEdgeSpec, NerveFaceSpec, PolyLawReadoutSpec, RPointProbeSpec,
    StaticLawReadoutSpec, SupportedNerveSpec, validate_diagnostics_task,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::solver::solve_diagnostics_task;
use num_bigint::BigUint;

fn prov() -> Provenance {
    Provenance::new(
        vec![SourceRef::new("test_diag", OriginKind::HumanAdopted)],
        vec![MathClause::G142A1],
    )
}

fn q_const(n: i64) -> PolyExpr {
    PolyExpr::Const(ScalarLit::rat(n, 1).unwrap())
}

fn z_lit(n: i64) -> ScalarLit {
    ScalarLit::int(n)
}

fn w2_nerve() -> SupportedNerveSpec {
    SupportedNerveSpec {
        charts: vec![
            ChartSupportSpec {
                name: "c0".into(),
                support: vec!["a".into(), "c".into(), "h".into()],
            },
            ChartSupportSpec {
                name: "c1".into(),
                support: vec!["a".into(), "b".into(), "h".into()],
            },
            ChartSupportSpec {
                name: "c2".into(),
                support: vec!["b".into(), "c".into(), "h".into()],
            },
        ],
        edges: vec![
            NerveEdgeSpec {
                name: "e01".into(),
                left: "c0".into(),
                right: "c1".into(),
            },
            NerveEdgeSpec {
                name: "e02".into(),
                left: "c0".into(),
                right: "c2".into(),
            },
            NerveEdgeSpec {
                name: "e12".into(),
                left: "c1".into(),
                right: "c2".into(),
            },
        ],
        faces: vec![NerveFaceSpec {
            name: "f012".into(),
            e0: "e01".into(),
            e1: "e02".into(),
            e2: "e12".into(),
        }],
    }
}

#[test]
fn w1_explicit_z_complex_nonflat_f2_and_nonfaithful_q() {
    let single_chart_nerve = SupportedNerveSpec {
        charts: vec![ChartSupportSpec {
            name: "c0".into(),
            support: vec!["s0".into(), "s2".into()],
        }],
        edges: Vec::new(),
        faces: Vec::new(),
    };
    let readout = DiagnosticsReadoutSpec::Static {
        sources: vec!["s0".into(), "s2".into()],
        targets: vec!["s0".into(), "s2".into()],
        reading: vec![("s0".into(), "s0".into()), ("s2".into(), "s2".into())],
        laws: vec![StaticLawReadoutSpec {
            law_name: "L".into(),
            values: vec![("s0".into(), z_lit(0)), ("s2".into(), z_lit(2))],
        }],
    };
    let explicit_k = ExplicitZComplexSpec {
        dim0: 1,
        dim1: 1,
        d0: vec![vec![2]],
        designated_cocycle: Some(vec![1]),
    };

    // 1. Z -> F_2: 非 flat 差（H^0(K ⊗ F_2) = F_2 != 0）と値域再生成（a -> (a, a)）。
    let task_f2 = validate_diagnostics_task(DiagnosticsTaskSpec {
        name: "w1_z_to_f2".into(),
        diagnostic_coeff: CoeffDomain::Z,
        nerve: single_chart_nerve.clone(),
        readout: readout.clone(),
        coeff_change: Some(CoeffChangeComparisonSpec {
            target_domain: CoeffDomain::Fp(BigUint::from(2u32)),
            compare_codomain_regeneration: true,
            explicit_z_complex: Some(explicit_k.clone()),
        }),
        collisions: Vec::new(),
        r_point_probe: None,
        dimension_realization: None,
        max_partitions: None,
        provenance: prov(),
    })
    .unwrap();
    let out_f2 = solve_diagnostics_task(&task_f2);
    assert_eq!(out_f2.verdict, Verdict::Established);
    let d_f2 = out_f2.diagnostics.as_ref().unwrap();
    assert!(d_f2.reading_adequate);
    assert!(d_f2.d1_d0_zero_verified);
    assert_eq!(d_f2.cell_dims, [2, 0, 0]);
    let cc_f2 = d_f2.coeff_change.as_ref().unwrap();
    assert!(!cc_f2.is_flat);
    assert!(!cc_f2.is_faithfully_flat);
    assert_eq!(cc_f2.fixed_label_c0_dim, 2);
    assert_eq!(cc_f2.fixed_label_h0_summary, "F_2^2");
    assert_eq!(cc_f2.regenerated_c0_dim, Some(1));
    assert_eq!(cc_f2.regenerated_h0_summary.as_deref(), Some("F_2"));
    assert_eq!(
        cc_f2.label_collision_map_description.as_deref(),
        Some("a -> (a, a)")
    );
    let ex_f2 = cc_f2.explicit_complex_check.as_ref().unwrap();
    assert_eq!(ex_f2.source_h0, "0");
    assert_eq!(ex_f2.source_h1, "Z/2");
    assert_eq!(ex_f2.target_h0, "F_2");
    assert_eq!(ex_f2.target_h1, "F_2");
    assert!(!ex_f2.flat_preservation_holds);

    // 2. Z -> Q: flat だが非 faithfully flat（torsion 類 [1] ∈ Z/2 が消失）。
    let task_q = validate_diagnostics_task(DiagnosticsTaskSpec {
        name: "w1_z_to_q".into(),
        diagnostic_coeff: CoeffDomain::Z,
        nerve: single_chart_nerve,
        readout,
        coeff_change: Some(CoeffChangeComparisonSpec {
            target_domain: CoeffDomain::Q,
            compare_codomain_regeneration: false,
            explicit_z_complex: Some(explicit_k),
        }),
        collisions: Vec::new(),
        r_point_probe: None,
        dimension_realization: None,
        max_partitions: None,
        provenance: prov(),
    })
    .unwrap();
    let out_q = solve_diagnostics_task(&task_q);
    assert_eq!(out_q.verdict, Verdict::Established);
    let cc_q = out_q.diagnostics.as_ref().unwrap().coeff_change.as_ref().unwrap();
    assert!(cc_q.is_flat);
    assert!(!cc_q.is_faithfully_flat);
    let ex_q = cc_q.explicit_complex_check.as_ref().unwrap();
    assert_eq!(ex_q.target_h0, "0");
    assert_eq!(ex_q.target_h1, "0");
    assert!(ex_q.flat_preservation_holds);
    assert_eq!(ex_q.designated_class_zero_in_source, Some(false));
    assert_eq!(ex_q.designated_class_zero_in_target, Some(true));
    assert_eq!(ex_q.torsion_vanished_in_target, Some(true));
}

#[test]
fn w1_three_edge_cycle_h1_over_z_q_fp() {
    let nerve = SupportedNerveSpec {
        charts: vec![
            ChartSupportSpec {
                name: "v0".into(),
                support: vec!["e20".into(), "e01".into()],
            },
            ChartSupportSpec {
                name: "v1".into(),
                support: vec!["e01".into(), "e12".into()],
            },
            ChartSupportSpec {
                name: "v2".into(),
                support: vec!["e12".into(), "e20".into()],
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
    };
    for (dom, expected_h1) in [
        (CoeffDomain::Z, "Z"),
        (CoeffDomain::Q, "Q"),
        (CoeffDomain::Fp(BigUint::from(5u32)), "F_5"),
    ] {
        let task = validate_diagnostics_task(DiagnosticsTaskSpec {
            name: format!("cycle_{dom}"),
            diagnostic_coeff: dom,
            nerve: nerve.clone(),
            readout: DiagnosticsReadoutSpec::Static {
                sources: vec!["e01".into(), "e12".into(), "e20".into()],
                targets: vec!["e01".into(), "e12".into(), "e20".into()],
                reading: vec![
                    ("e01".into(), "e01".into()),
                    ("e12".into(), "e12".into()),
                    ("e20".into(), "e20".into()),
                ],
                laws: vec![StaticLawReadoutSpec {
                    law_name: "p".into(),
                    values: vec![
                        ("e01".into(), z_lit(0)),
                        ("e12".into(), z_lit(0)),
                        ("e20".into(), z_lit(0)),
                    ],
                }],
            },
            coeff_change: None,
            collisions: Vec::new(),
            r_point_probe: None,
            dimension_realization: None,
            max_partitions: None,
            provenance: prov(),
        })
        .unwrap();
        let out = solve_diagnostics_task(&task);
        assert_eq!(out.verdict, Verdict::Established);
        let d = out.diagnostics.as_ref().unwrap();
        assert!(d.d1_d0_zero_verified);
        assert_eq!(d.h1_free_rank, 1);
        assert!(d.h1_torsion.is_empty());
        assert_eq!(d.h1_summary, expected_h1);
        assert_eq!(d.block_decomposition.len(), 1);
        assert_eq!(d.block_decomposition[0].h1_free_rank, 1);
    }
}

#[test]
fn w2_stratification_mv_r_point_and_upper_semicontinuity() {
    for diag_coeff in [
        CoeffDomain::Q,
        CoeffDomain::Z,
        CoeffDomain::Fp(BigUint::from(3u32)),
    ] {
        let task = validate_diagnostics_task(DiagnosticsTaskSpec {
            name: format!("w2_{diag_coeff}"),
            diagnostic_coeff: diag_coeff,
            nerve: w2_nerve(),
            readout: DiagnosticsReadoutSpec::Polynomial {
                base_domain: CoeffDomain::Q,
                base_vars: vec!["lambda".into(), "mu".into()],
                base_relations: Vec::new(),
                sources: vec!["a".into(), "b".into(), "c".into(), "h".into()],
                laws: vec![PolyLawReadoutSpec {
                    law_name: "L".into(),
                    values: vec![
                        ("a".into(), q_const(0)),
                        ("b".into(), PolyExpr::StateVar("lambda".into())),
                        ("c".into(), q_const(0)),
                        ("h".into(), PolyExpr::StateVar("mu".into())),
                    ],
                }],
            },
            coeff_change: None,
            collisions: vec![
                // 生成: mu=1, lambda -> 0
                CollisionComparisonSpec {
                    label: "generation".into(),
                    law_name: "L".into(),
                    fine_partition: vec![
                        vec!["a".into(), "c".into()],
                        vec!["b".into()],
                        vec!["h".into()],
                    ],
                    coarse_partition: vec![
                        vec!["a".into(), "b".into(), "c".into()],
                        vec!["h".into()],
                    ],
                    alternative_merge_paths: Vec::new(),
                },
                // 消失: lambda=0, mu -> 0
                CollisionComparisonSpec {
                    label: "vanishing".into(),
                    law_name: "L".into(),
                    fine_partition: vec![
                        vec!["a".into(), "b".into(), "c".into()],
                        vec!["h".into()],
                    ],
                    coarse_partition: vec![vec![
                        "a".into(),
                        "b".into(),
                        "c".into(),
                        "h".into(),
                    ]],
                    alternative_merge_paths: Vec::new(),
                },
                // C2 多段合流の順序独立性: {{a,c},{b},{h}} -> {{a,b,c,h}} を 2 経路で合成比較
                CollisionComparisonSpec {
                    label: "multi_stage_full".into(),
                    law_name: "L".into(),
                    fine_partition: vec![
                        vec!["a".into(), "c".into()],
                        vec!["b".into()],
                        vec!["h".into()],
                    ],
                    coarse_partition: vec![vec![
                        "a".into(),
                        "b".into(),
                        "c".into(),
                        "h".into(),
                    ]],
                    alternative_merge_paths: vec![
                        vec![vec![
                            vec!["a".into(), "b".into(), "c".into()],
                            vec!["h".into()],
                        ]],
                        vec![vec![
                            vec!["a".into(), "c".into()],
                            vec!["b".into(), "h".into()],
                        ]],
                    ],
                },
            ],
            r_point_probe: Some(RPointProbeSpec {
                ring_var: "eps".into(),
                ring_max_deg: 1,
                points: vec![
                    NamedRPointSpec {
                        label: "origin".into(),
                        coords: vec![
                            ("lambda".into(), vec![q_const(0), q_const(0)]),
                            ("mu".into(), vec![q_const(0), q_const(0)]),
                        ],
                    },
                    NamedRPointSpec {
                        label: "nilpotent_mu".into(),
                        coords: vec![
                            ("lambda".into(), vec![q_const(0), q_const(0)]),
                            ("mu".into(), vec![q_const(0), q_const(1)]),
                        ],
                    },
                ],
            }),
            dimension_realization: None,
            max_partitions: None,
            provenance: prov(),
        })
        .unwrap();

        let out = solve_diagnostics_task(&task);
        assert_eq!(out.verdict, Verdict::Established);
        let d = out.diagnostics.as_ref().unwrap();
        assert!(d.d1_d0_zero_verified);

        // 5 非空 stratum が得られ、V(lambda) ∩ D(mu) のみ H^1 = 1。
        assert_eq!(d.strata.len(), 5);
        let h1_ones: Vec<_> = d.strata.iter().filter(|s| s.h1_free_rank == 1).collect();
        assert_eq!(h1_ones.len(), 1);
        assert_eq!(h1_ones[0].partition.len(), 2);
        assert!(d.strata.iter().filter(|s| s.h1_free_rank == 0).count() == 4);

        // 生成・消失・多段合流
        let gen_col = &d.collisions[0];
        assert_eq!(gen_col.label, "generation");
        assert_eq!(gen_col.ker_h1_r_dim, 1);
        assert_eq!(gen_col.coker_h0_rho_dim, 1);
        assert_eq!(gen_col.coker_h1_r_dim, 0);
        assert_eq!(gen_col.im_h1_rho_dim, 0);
        assert!(gen_col.mayer_vietoris_identity_verified);
        assert!(!gen_col.h1_r_is_isomorphism);

        let van = &d.collisions[1];
        assert_eq!(van.label, "vanishing");
        assert_eq!(van.ker_h1_r_dim, 0);
        assert_eq!(van.coker_h0_rho_dim, 0);
        assert_eq!(van.coker_h1_r_dim, 1);
        assert_eq!(van.im_h1_rho_dim, 1);
        assert!(van.mayer_vietoris_identity_verified);
        assert!(!van.h1_r_is_isomorphism);

        let multi = &d.collisions[2];
        assert!(multi.mayer_vietoris_identity_verified);
        assert_eq!(multi.multi_stage_order_independent, Some(true));

        // D3 上半連続性反証
        let refut = d.upper_semicontinuity_refutation.as_ref().unwrap();
        assert_eq!(refut.generic_h1_dim, 1);
        assert_eq!(refut.special_h1_dim, 0);
        assert!(refut.pseudo_coherent_complex_excluded);

        // W2 R-点対照
        let rp = d.r_point_contrast.as_ref().unwrap();
        assert!(rp.r_values_differ);
        assert!(rp.geometric_stalks_agree);
        assert_eq!(rp.geometric_stalk_h1_dims.get("origin"), Some(&0));
        assert_eq!(rp.geometric_stalk_h1_dims.get("nilpotent_mu"), Some(&0));
    }
}

#[test]
fn d1_general_locally_closed_dimension_realization() {
    let base_nerve = SupportedNerveSpec {
        charts: vec![ChartSupportSpec {
            name: "c0".into(),
            support: vec!["s0".into()],
        }],
        edges: Vec::new(),
        faces: Vec::new(),
    };
    // r = 3 (g1 = x, g2 = y - 1, g3 = x + z), h = w -> cycle_vertices = max(3, 4) = 4
    let task = validate_diagnostics_task(DiagnosticsTaskSpec {
        name: "d1_general".into(),
        diagnostic_coeff: CoeffDomain::Q,
        nerve: base_nerve,
        readout: DiagnosticsReadoutSpec::Static {
            sources: vec!["s0".into()],
            targets: vec!["s0".into()],
            reading: vec![("s0".into(), "s0".into())],
            laws: vec![StaticLawReadoutSpec {
                law_name: "L".into(),
                values: vec![("s0".into(), z_lit(0))],
            }],
        },
        coeff_change: None,
        collisions: Vec::new(),
        r_point_probe: None,
        dimension_realization: Some(DimensionRealizationSpec {
            base_domain: CoeffDomain::Q,
            base_vars: vec!["x".into(), "y".into(), "z".into(), "w".into()],
            vanishing_polys: vec![
                NamedPoly {
                    name: "g1".into(),
                    expr: PolyExpr::StateVar("x".into()),
                    provenance: None,
                },
                NamedPoly {
                    name: "g2".into(),
                    expr: PolyExpr::Sub(
                        Box::new(PolyExpr::StateVar("y".into())),
                        Box::new(q_const(1)),
                    ),
                    provenance: None,
                },
                NamedPoly {
                    name: "g3".into(),
                    expr: PolyExpr::Add(
                        Box::new(PolyExpr::StateVar("x".into())),
                        Box::new(PolyExpr::StateVar("z".into())),
                    ),
                    provenance: None,
                },
            ],
            invertible_poly: NamedPoly {
                name: "h".into(),
                expr: PolyExpr::StateVar("w".into()),
                provenance: None,
            },
            probe_points: vec![
                NamedBasePointSpec {
                    label: "inside".into(),
                    coords: vec![
                        ("x".into(), q_const(0)),
                        ("y".into(), q_const(1)),
                        ("z".into(), q_const(0)),
                        ("w".into(), q_const(2)),
                    ],
                },
                NamedBasePointSpec {
                    label: "h_zero".into(),
                    coords: vec![
                        ("x".into(), q_const(0)),
                        ("y".into(), q_const(1)),
                        ("z".into(), q_const(0)),
                        ("w".into(), q_const(0)),
                    ],
                },
                NamedBasePointSpec {
                    label: "g2_nonzero".into(),
                    coords: vec![
                        ("x".into(), q_const(0)),
                        ("y".into(), q_const(2)),
                        ("z".into(), q_const(0)),
                        ("w".into(), q_const(2)),
                    ],
                },
                NamedBasePointSpec {
                    label: "g3_nonzero".into(),
                    coords: vec![
                        ("x".into(), q_const(0)),
                        ("y".into(), q_const(1)),
                        ("z".into(), q_const(3)),
                        ("w".into(), q_const(5)),
                    ],
                },
            ],
        }),
        max_partitions: None,
        provenance: prov(),
    })
    .unwrap();

    let out = solve_diagnostics_task(&task);
    assert_eq!(out.verdict, Verdict::Established);
    let dr = out.diagnostics.unwrap().dimension_realization.unwrap();
    assert_eq!(dr.cycle_vertices, 4);
    assert!(dr.all_probes_matched);
    assert_eq!(dr.probe_results[0].expected_indicator, 1);
    assert_eq!(dr.probe_results[0].computed_h1_dim, 1);
    assert_eq!(dr.probe_results[1].computed_h1_dim, 0);
    assert_eq!(dr.probe_results[2].computed_h1_dim, 0);
    assert_eq!(dr.probe_results[3].computed_h1_dim, 0);
}

#[test]
fn diagnostics_silence_inadequate_reading_max_partitions_unobserved_and_bad_ring_hom() {
    // 1. Adequacy 違反 -> Undetermined
    let task_inadeq = validate_diagnostics_task(DiagnosticsTaskSpec {
        name: "inadequate".into(),
        diagnostic_coeff: CoeffDomain::Q,
        nerve: SupportedNerveSpec {
            charts: vec![ChartSupportSpec {
                name: "c0".into(),
                support: vec!["t0".into()],
            }],
            edges: Vec::new(),
            faces: Vec::new(),
        },
        readout: DiagnosticsReadoutSpec::Static {
            sources: vec!["s0".into(), "s1".into()],
            targets: vec!["t0".into()],
            reading: vec![("s0".into(), "t0".into()), ("s1".into(), "t0".into())],
            laws: vec![StaticLawReadoutSpec {
                law_name: "L".into(),
                values: vec![("s0".into(), z_lit(0)), ("s1".into(), z_lit(1))],
            }],
        },
        coeff_change: None,
        collisions: Vec::new(),
        r_point_probe: None,
        dimension_realization: None,
        max_partitions: None,
        provenance: prov(),
    })
    .unwrap();
    let out_inadeq = solve_diagnostics_task(&task_inadeq);
    assert!(matches!(
        out_inadeq.verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { ref condition, .. })
            if condition == "reading_adequacy"
    ));

    // 2. max_partitions 超過 -> DiagnosticsStratificationOutOfScope
    let task_cap = validate_diagnostics_task(DiagnosticsTaskSpec {
        name: "cap_exceeded".into(),
        diagnostic_coeff: CoeffDomain::Q,
        nerve: w2_nerve(),
        readout: DiagnosticsReadoutSpec::Polynomial {
            base_domain: CoeffDomain::Q,
            base_vars: vec!["lambda".into(), "mu".into()],
            base_relations: Vec::new(),
            sources: vec!["a".into(), "b".into(), "c".into(), "h".into()],
            laws: vec![PolyLawReadoutSpec {
                law_name: "L".into(),
                values: vec![
                    ("a".into(), q_const(0)),
                    ("b".into(), PolyExpr::StateVar("lambda".into())),
                    ("c".into(), q_const(0)),
                    ("h".into(), PolyExpr::StateVar("mu".into())),
                ],
            }],
        },
        coeff_change: None,
        collisions: Vec::new(),
        r_point_probe: None,
        dimension_realization: None,
        max_partitions: Some(2),
        provenance: prov(),
    })
    .unwrap();
    let out_cap = solve_diagnostics_task(&task_cap);
    assert!(matches!(
        out_cap.verdict,
        Verdict::Undetermined(SilenceReason::DiagnosticsStratificationOutOfScope { .. })
    ));

    // 3. Unobserved 依存 -> UnobservedDependency
    let task_unobs = validate_diagnostics_task(DiagnosticsTaskSpec {
        name: "unobs_diag".into(),
        diagnostic_coeff: CoeffDomain::Q,
        nerve: w2_nerve(),
        readout: DiagnosticsReadoutSpec::Polynomial {
            base_domain: CoeffDomain::Q,
            base_vars: vec!["lambda".into()],
            base_relations: Vec::new(),
            sources: vec!["a".into(), "b".into(), "c".into(), "h".into()],
            laws: vec![PolyLawReadoutSpec {
                law_name: "L".into(),
                values: vec![
                    ("a".into(), q_const(0)),
                    ("b".into(), PolyExpr::Unobserved {
                        slot: "missing_readout".into(),
                        origin: Some(SourceRef::new("m", OriginKind::LlmCandidate)),
                    }),
                    ("c".into(), q_const(0)),
                    ("h".into(), PolyExpr::StateVar("lambda".into())),
                ],
            }],
        },
        coeff_change: None,
        collisions: Vec::new(),
        r_point_probe: None,
        dimension_realization: None,
        max_partitions: None,
        provenance: prov(),
    })
    .unwrap();
    let out_unobs = solve_diagnostics_task(&task_unobs);
    assert!(matches!(
        out_unobs.verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { .. })
    ));

    // 4. Q -> F_2 環射不在 -> Undetermined
    let task_bad_hom = validate_diagnostics_task(DiagnosticsTaskSpec {
        name: "bad_hom".into(),
        diagnostic_coeff: CoeffDomain::Q,
        nerve: SupportedNerveSpec {
            charts: vec![ChartSupportSpec {
                name: "c0".into(),
                support: vec!["s0".into()],
            }],
            edges: Vec::new(),
            faces: Vec::new(),
        },
        readout: DiagnosticsReadoutSpec::Static {
            sources: vec!["s0".into()],
            targets: vec!["s0".into()],
            reading: vec![("s0".into(), "s0".into())],
            laws: vec![StaticLawReadoutSpec {
                law_name: "L".into(),
                values: vec![("s0".into(), z_lit(0))],
            }],
        },
        coeff_change: Some(CoeffChangeComparisonSpec {
            target_domain: CoeffDomain::Fp(BigUint::from(2u32)),
            compare_codomain_regeneration: false,
            explicit_z_complex: None,
        }),
        collisions: Vec::new(),
        r_point_probe: None,
        dimension_realization: None,
        max_partitions: None,
        provenance: prov(),
    })
    .unwrap();
    let out_bad_hom = solve_diagnostics_task(&task_bad_hom);
    assert!(matches!(
        out_bad_hom.verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { ref condition, .. })
            if condition == "ring_homomorphism_exists"
    ));

    // 5. Static reading 非整合な collision partition は暗黙上書きせず fail-closed 沈黙（Finding 2）
    let task_bad_col = validate_diagnostics_task(DiagnosticsTaskSpec {
        name: "bad_col_adequacy".into(),
        diagnostic_coeff: CoeffDomain::Q,
        nerve: SupportedNerveSpec {
            charts: vec![ChartSupportSpec {
                name: "c0".into(),
                support: vec!["t0".into()],
            }],
            edges: Vec::new(),
            faces: Vec::new(),
        },
        readout: DiagnosticsReadoutSpec::Static {
            sources: vec!["s0".into(), "s1".into()],
            targets: vec!["t0".into()],
            reading: vec![("s0".into(), "t0".into()), ("s1".into(), "t0".into())],
            laws: vec![StaticLawReadoutSpec {
                law_name: "L".into(),
                values: vec![("s0".into(), z_lit(0)), ("s1".into(), z_lit(0))],
            }],
        },
        coeff_change: None,
        collisions: vec![CollisionComparisonSpec {
            label: "split_same_target".into(),
            law_name: "L".into(),
            fine_partition: vec![vec!["s0".into()], vec!["s1".into()]],
            coarse_partition: vec![vec!["s0".into(), "s1".into()]],
            alternative_merge_paths: Vec::new(),
        }],
        r_point_probe: None,
        dimension_realization: None,
        max_partitions: None,
        provenance: prov(),
    })
    .unwrap();
    assert!(matches!(
        solve_diagnostics_task(&task_bad_col).verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { ref condition, .. })
            if condition == "collision_partition_reading_adequacy"
    ));

    // 6. 自由類 [2] ∈ H^1([Z --0--> Z]) = Z の mod 2 消失は torsion_vanished_in_target = false（Finding 5）
    let task_free_mod2 = validate_diagnostics_task(DiagnosticsTaskSpec {
        name: "free_class_mod2".into(),
        diagnostic_coeff: CoeffDomain::Z,
        nerve: SupportedNerveSpec {
            charts: vec![ChartSupportSpec {
                name: "c0".into(),
                support: vec!["s0".into()],
            }],
            edges: Vec::new(),
            faces: Vec::new(),
        },
        readout: DiagnosticsReadoutSpec::Static {
            sources: vec!["s0".into()],
            targets: vec!["s0".into()],
            reading: vec![("s0".into(), "s0".into())],
            laws: vec![StaticLawReadoutSpec {
                law_name: "L".into(),
                values: vec![("s0".into(), z_lit(0))],
            }],
        },
        coeff_change: Some(CoeffChangeComparisonSpec {
            target_domain: CoeffDomain::Fp(BigUint::from(2u32)),
            compare_codomain_regeneration: false,
            explicit_z_complex: Some(ExplicitZComplexSpec {
                dim0: 1,
                dim1: 1,
                d0: vec![vec![0]],
                designated_cocycle: Some(vec![2]),
            }),
        }),
        collisions: Vec::new(),
        r_point_probe: None,
        dimension_realization: None,
        max_partitions: None,
        provenance: prov(),
    })
    .unwrap();
    let ex_free = solve_diagnostics_task(&task_free_mod2)
        .diagnostics
        .unwrap()
        .coeff_change
        .unwrap()
        .explicit_complex_check
        .unwrap();
    assert_eq!(ex_free.designated_class_zero_in_source, Some(false));
    assert_eq!(ex_free.designated_class_zero_in_target, Some(true));
    assert_eq!(ex_free.torsion_vanished_in_target, Some(false));
}

#[test]
fn fp_base_stratification_r_point_and_fail_closed_boundaries() {
    let z_const = |n: i64| PolyExpr::Const(ScalarLit::int(n));
    let fp5_const = |n: u32| {
        PolyExpr::Const(ScalarLit::Fp {
            value: BigUint::from(n % 5),
            modulus: BigUint::from(5u32),
        })
    };
    // 1. F_5 基底での W2 層別・D3 上半連続性反証・R-点対照
    let fp5 = CoeffDomain::Fp(BigUint::from(5u32));
    let task_fp = validate_diagnostics_task(DiagnosticsTaskSpec {
        name: "w2_base_f5".into(),
        diagnostic_coeff: CoeffDomain::Q,
        nerve: w2_nerve(),
        readout: DiagnosticsReadoutSpec::Polynomial {
            base_domain: fp5.clone(),
            base_vars: vec!["lambda".into(), "mu".into()],
            base_relations: Vec::new(),
            sources: vec!["a".into(), "b".into(), "c".into(), "h".into()],
            laws: vec![PolyLawReadoutSpec {
                law_name: "L".into(),
                values: vec![
                    ("a".into(), fp5_const(0)),
                    ("b".into(), PolyExpr::StateVar("lambda".into())),
                    ("c".into(), fp5_const(0)),
                    ("h".into(), PolyExpr::StateVar("mu".into())),
                ],
            }],
        },
        coeff_change: None,
        collisions: Vec::new(),
        r_point_probe: Some(RPointProbeSpec {
            ring_var: "eps".into(),
            ring_max_deg: 1,
            points: vec![
                NamedRPointSpec {
                    label: "origin".into(),
                    coords: vec![
                        ("lambda".into(), vec![fp5_const(0), fp5_const(0)]),
                        ("mu".into(), vec![fp5_const(0), fp5_const(0)]),
                    ],
                },
                NamedRPointSpec {
                    label: "dual_mu".into(),
                    coords: vec![
                        ("lambda".into(), vec![fp5_const(0), fp5_const(0)]),
                        ("mu".into(), vec![fp5_const(0), fp5_const(1)]),
                    ],
                },
            ],
        }),
        dimension_realization: None,
        max_partitions: None,
        provenance: prov(),
    })
    .unwrap();
    let out_fp = solve_diagnostics_task(&task_fp);
    assert_eq!(out_fp.verdict, Verdict::Established);
    let d_fp = out_fp.diagnostics.unwrap();
    assert_eq!(d_fp.strata.len(), 5);
    assert!(d_fp.strata.iter().any(|s| s.h1_free_rank == 1));
    let refut = d_fp.upper_semicontinuity_refutation.as_ref().unwrap();
    assert_eq!(refut.generic_h1_dim, 1);
    assert_eq!(refut.special_h1_dim, 0);
    let rp = d_fp.r_point_contrast.unwrap();
    assert!(rp.r_values_differ);
    assert!(rp.geometric_stalks_agree);

    // 2. F_5 非線形 base_relations + 非空不等号での D3 飽和は fail-closed 沈黙
    let task_fp_nonlin = validate_diagnostics_task(DiagnosticsTaskSpec {
        name: "fp5_nonlinear_closure".into(),
        diagnostic_coeff: CoeffDomain::Q,
        nerve: w2_nerve(),
        readout: DiagnosticsReadoutSpec::Polynomial {
            base_domain: fp5,
            base_vars: vec!["lambda".into(), "mu".into()],
            base_relations: vec![NamedPoly {
                name: "curve".into(),
                expr: PolyExpr::Sub(
                    Box::new(PolyExpr::Mul(
                        Box::new(PolyExpr::StateVar("lambda".into())),
                        Box::new(PolyExpr::StateVar("mu".into())),
                    )),
                    Box::new(PolyExpr::Mul(
                        Box::new(PolyExpr::StateVar("lambda".into())),
                        Box::new(PolyExpr::StateVar("lambda".into())),
                    )),
                ),
                provenance: None,
            }],
            sources: vec!["a".into(), "b".into(), "c".into(), "h".into()],
            laws: vec![PolyLawReadoutSpec {
                law_name: "L".into(),
                values: vec![
                    ("a".into(), fp5_const(0)),
                    ("b".into(), PolyExpr::StateVar("lambda".into())),
                    ("c".into(), fp5_const(0)),
                    ("h".into(), PolyExpr::StateVar("mu".into())),
                ],
            }],
        },
        coeff_change: None,
        collisions: Vec::new(),
        r_point_probe: None,
        dimension_realization: None,
        max_partitions: None,
        provenance: prov(),
    })
    .unwrap();
    assert!(matches!(
        solve_diagnostics_task(&task_fp_nonlin).verdict,
        Verdict::Undetermined(SilenceReason::DiagnosticsStratificationOutOfScope { .. })
    ));

    // 3. base_domain = Z の多項式層別は fail-closed 沈黙
    let task_z_base = validate_diagnostics_task(DiagnosticsTaskSpec {
        name: "z_base_strat_out_of_scope".into(),
        diagnostic_coeff: CoeffDomain::Q,
        nerve: w2_nerve(),
        readout: DiagnosticsReadoutSpec::Polynomial {
            base_domain: CoeffDomain::Z,
            base_vars: vec!["lambda".into()],
            base_relations: Vec::new(),
            sources: vec!["a".into(), "b".into(), "c".into(), "h".into()],
            laws: vec![PolyLawReadoutSpec {
                law_name: "L".into(),
                values: vec![
                    ("a".into(), z_const(0)),
                    ("b".into(), PolyExpr::StateVar("lambda".into())),
                    ("c".into(), z_const(0)),
                    ("h".into(), z_const(1)),
                ],
            }],
        },
        coeff_change: None,
        collisions: Vec::new(),
        r_point_probe: None,
        dimension_realization: None,
        max_partitions: None,
        provenance: prov(),
    })
    .unwrap();
    assert!(matches!(
        solve_diagnostics_task(&task_z_base).verdict,
        Verdict::Undetermined(SilenceReason::DiagnosticsStratificationOutOfScope { .. })
    ));

    // 4. diagnostic_coeff != Z に explicit_z_complex を渡すと fail-closed 沈黙
    let task_bad_ex = validate_diagnostics_task(DiagnosticsTaskSpec {
        name: "explicit_z_on_f2_source".into(),
        diagnostic_coeff: CoeffDomain::Fp(BigUint::from(2u32)),
        nerve: SupportedNerveSpec {
            charts: vec![ChartSupportSpec {
                name: "c0".into(),
                support: vec!["s0".into()],
            }],
            edges: Vec::new(),
            faces: Vec::new(),
        },
        readout: DiagnosticsReadoutSpec::Static {
            sources: vec!["s0".into()],
            targets: vec!["s0".into()],
            reading: vec![("s0".into(), "s0".into())],
            laws: vec![StaticLawReadoutSpec {
                law_name: "L".into(),
                values: vec![("s0".into(), z_lit(0))],
            }],
        },
        coeff_change: Some(CoeffChangeComparisonSpec {
            target_domain: CoeffDomain::Fp(BigUint::from(2u32)),
            compare_codomain_regeneration: false,
            explicit_z_complex: Some(ExplicitZComplexSpec {
                dim0: 1,
                dim1: 1,
                d0: vec![vec![2]],
                designated_cocycle: Some(vec![1]),
            }),
        }),
        collisions: Vec::new(),
        r_point_probe: None,
        dimension_realization: None,
        max_partitions: None,
        provenance: prov(),
    })
    .unwrap();
    assert!(matches!(
        solve_diagnostics_task(&task_bad_ex).verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { ref condition, .. })
            if condition == "explicit_z_complex_requires_z_source"
    ));
}
