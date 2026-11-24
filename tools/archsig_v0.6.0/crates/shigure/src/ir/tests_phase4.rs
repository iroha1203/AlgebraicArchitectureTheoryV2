//! Phase 4 IR（`lift`・`artin`・`diagnostics`・`atlas`・`result_phase4`）の構築・検証・JSON 出力単体テスト（AC1）。

use crate::ir::artin::{
    ArtinTaskSpec, AuxiliaryDefSpec, CompositeStageSpec, validate_artin_task,
};
use crate::ir::atlas::{
    AtlasRefinementSpec, AtlasTaskSpec, AtomicOpCompareSpec, ExtendedLanguageCheckSpec,
    ExtendedOperationCheckSpec, GraphEdgeSpec, validate_atlas_task,
};
use crate::ir::change::{NamedPoly, PointDomain};
use crate::ir::diagnostics::{
    ChartSupportSpec, CollisionComparisonSpec, DiagnosticsReadoutSpec, DiagnosticsTaskSpec,
    NerveEdgeSpec, NerveFaceSpec, StaticLawReadoutSpec, SupportedNerveSpec,
    validate_diagnostics_task,
};
use crate::ir::lift::{
    DeclarationContextSpec, DeclarationCoverSpec, LiftTaskSpec, RelativeReadingSpec, RingParamSpec,
    SquareZeroSpec, TwoContextCechSpec, validate_lift_task,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_phase4::{
    ArtinOutcomeDetail, AtlasOutcomeDetail, ConstrainedRepairSummary, DiagnosticsOutcomeDetail,
    ExtendedCheckOutcome, ExtendedLanguageResult, LiftOutcomeDetail,
};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::ir::validate::ValidationError;
use archsig_common::canonical::Json;
use num_bigint::BigInt;
use std::collections::BTreeMap;

fn sample_prov() -> Provenance {
    Provenance::new(
        vec![SourceRef::new("phase4:test", OriginKind::HumanAdopted)],
        vec![MathClause::G141E2],
    )
}

#[test]
fn lift_task_validation_checks_dims_vars_and_provenance() {
    let valid = LiftTaskSpec {
        name: "h2_t2".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["t".into()],
        ring_params: vec![],
        laws: vec![NamedPoly {
            name: "t_sq".into(),
            expr: PolyExpr::Pow(Box::new(PolyExpr::StateVar("t".into())), 2),
            provenance: None,
        }],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 1,
        },
        base_point: vec![(
            "t".into(),
            vec![
                PolyExpr::Const(ScalarLit::Z(BigInt::from(0))),
                PolyExpr::Const(ScalarLit::Z(BigInt::from(1))),
            ],
        )],
        ambient_lift: None,
        relative_reading: None,
        declaration_cover: None,
        affine_allowed: None,
        redundant_comparison: None,
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: sample_prov(),
    };
    assert!(validate_lift_task(valid.clone()).is_ok());

    let mut bad_dim = valid.clone();
    bad_dim.base_point[0].1.pop();
    assert!(matches!(
        validate_lift_task(bad_dim),
        Err(ValidationError::ConversionError { .. })
    ));

    // 未宣言変数を参照する Law は拒否
    let mut bad_var = valid.clone();
    bad_var.laws[0].expr = PolyExpr::StateVar("undeclared".into());
    assert!(matches!(
        validate_lift_task(bad_var),
        Err(ValidationError::UnknownRef { .. })
    ));

    // 不正な SourceRef span (start > end) は拒否
    let mut bad_span = valid;
    bad_span.provenance.origins[0].span = Some((10, 2));
    assert!(matches!(
        validate_lift_task(bad_span),
        Err(ValidationError::InvalidSourceSpan { .. })
    ));
}

#[test]
fn artin_task_validation_enforces_acyclic_aux_and_f6_composite_stage() {
    let valid = ArtinTaskSpec {
        name: "h5_chain".into(),
        coeff_domain: CoeffDomain::Q,
        obs_vars: vec!["t".into()],
        obs_relations: vec![],
        aux_defs: vec![
            AuxiliaryDefSpec {
                name: "y1".into(),
                expr: PolyExpr::Pow(Box::new(PolyExpr::StateVar("t".into())), 2),
            },
            AuxiliaryDefSpec {
                name: "y2".into(),
                expr: PolyExpr::Pow(Box::new(PolyExpr::StateVar("y1".into())), 2),
            },
        ],
        extra_laws: vec![NamedPoly {
            name: "y2_zero".into(),
            expr: PolyExpr::StateVar("y2".into()),
            provenance: None,
        }],
        base_point: vec![("t".into(), PolyExpr::Const(ScalarLit::Z(BigInt::from(0))))],
        max_order: 8,
        max_artin_dim: None,
        // F6: 第 2 段が第 1 段の補助変数 y1 を参照できる
        composite_stage: Some(CompositeStageSpec {
            aux_defs: vec![AuxiliaryDefSpec {
                name: "z1".into(),
                expr: PolyExpr::Mul(
                    Box::new(PolyExpr::StateVar("y1".into())),
                    Box::new(PolyExpr::StateVar("t".into())),
                ),
            }],
            extra_laws: vec![NamedPoly {
                name: "z1_zero".into(),
                expr: PolyExpr::StateVar("z1".into()),
                provenance: None,
            }],
        }),
        base_change: None,
        non_noetherian_infinite: false,
        provenance: sample_prov(),
    };
    let checked = validate_artin_task(valid.clone()).unwrap();
    assert!(checked.is_free_observation_chart());

    // 第 2 段で第 1 段と同名の補助変数をシャドーイングすると DuplicateDecl で拒否
    let mut shadow = valid.clone();
    shadow.composite_stage.as_mut().unwrap().aux_defs[0].name = "y1".into();
    assert!(matches!(
        validate_artin_task(shadow),
        Err(ValidationError::DuplicateDecl { .. })
    ));

    // 循環・逆順参照（y1 がまだ未定義の y2 を参照）は拒否される
    let mut cyclic = valid;
    cyclic.aux_defs[0].expr = PolyExpr::StateVar("y2".into());
    assert!(matches!(
        validate_artin_task(cyclic),
        Err(ValidationError::UnknownRef { .. })
    ));
}

#[test]
fn diagnostics_task_validation_enforces_k1_endpoints_and_collision_coarsening() {
    let nerve_ok = SupportedNerveSpec {
        charts: vec![
            ChartSupportSpec {
                name: "c0".into(),
                support: vec!["s0".into(), "s1".into()],
            },
            ChartSupportSpec {
                name: "c1".into(),
                support: vec!["s0".into()],
            },
            ChartSupportSpec {
                name: "c2".into(),
                support: vec!["s0".into()],
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
    };
    let make_spec = |nerve: SupportedNerveSpec, collisions: Vec<CollisionComparisonSpec>| {
        DiagnosticsTaskSpec {
            name: "k1_check".into(),
            diagnostic_coeff: CoeffDomain::Z,
            nerve,
            readout: DiagnosticsReadoutSpec::Static {
                sources: vec!["s0".into(), "s1".into()],
                targets: vec!["s0".into(), "s1".into()],
                reading: vec![("s0".into(), "s0".into()), ("s1".into(), "s1".into())],
                laws: vec![StaticLawReadoutSpec {
                    law_name: "L".into(),
                    values: vec![
                        ("s0".into(), ScalarLit::Z(BigInt::from(0))),
                        ("s1".into(), ScalarLit::Z(BigInt::from(1))),
                    ],
                }],
            },
            coeff_change: None,
            collisions,
            r_point_probe: None,
            dimension_realization: None,
            max_partitions: None,
            provenance: sample_prov(),
        }
    };
    assert!(validate_diagnostics_task(make_spec(nerve_ok.clone(), vec![])).is_ok());

    // coarse が fine の粗化でない（逆に細分化になっている）場合は拒否
    let bad_coarsen = CollisionComparisonSpec {
        label: "bad".into(),
        law_name: "L".into(),
        fine_partition: vec![vec!["s0".into(), "s1".into()]],
        coarse_partition: vec![vec!["s0".into()], vec!["s1".into()]],
        alternative_merge_paths: vec![],
    };
    assert!(matches!(
        validate_diagnostics_task(make_spec(nerve_ok.clone(), vec![bad_coarsen])),
        Err(ValidationError::ConversionError { .. })
    ));

    // e1 と e2 を入れ替えると K1 端点等式 r(e0) == l(e2) が破れるため拒否
    let mut nerve_bad = nerve_ok;
    nerve_bad.faces[0].e1 = "e12".into();
    nerve_bad.faces[0].e2 = "e02".into();
    assert!(matches!(
        validate_diagnostics_task(make_spec(nerve_bad, vec![])),
        Err(ValidationError::ConversionError { .. })
    ));
}

#[test]
fn atlas_task_validation_enforces_simple_graph_nerve_map_and_general_extended_lang() {
    let valid = AtlasTaskSpec {
        name: "tri".into(),
        coeff_domain: CoeffDomain::Z,
        vertices: vec!["v0".into(), "v1".into(), "v2".into()],
        edges: vec![
            GraphEdgeSpec {
                name: "e01".into(),
                from: "v0".into(),
                to: "v1".into(),
                offset: PolyExpr::Const(ScalarLit::Z(BigInt::from(1))),
            },
            GraphEdgeSpec {
                name: "e12".into(),
                from: "v1".into(),
                to: "v2".into(),
                offset: PolyExpr::Const(ScalarLit::Z(BigInt::from(2))),
            },
            GraphEdgeSpec {
                name: "e20".into(),
                from: "v2".into(),
                to: "v0".into(),
                offset: PolyExpr::Const(ScalarLit::Z(BigInt::from(-3))),
            },
        ],
        mu: PolyExpr::Const(ScalarLit::Z(BigInt::from(1))),
        base_lambdas: vec![
            ("v0".into(), PolyExpr::Const(ScalarLit::Z(BigInt::from(0)))),
            ("v1".into(), PolyExpr::Const(ScalarLit::Z(BigInt::from(0)))),
            ("v2".into(), PolyExpr::Const(ScalarLit::Z(BigInt::from(0)))),
        ],
        allowed_vertices: vec!["v0".into(), "v1".into(), "v2".into()],
        allowed_edges: vec!["e01".into(), "e12".into(), "e20".into()],
        compare_to_q: true,
        refinement: None,
        extended_language_check: Some(ExtendedLanguageCheckSpec {
            state_vars: vec!["B".into(), "C".into()],
            adapter_map: vec![
                (
                    "B".into(),
                    PolyExpr::Add(
                        Box::new(PolyExpr::StateVar("B".into())),
                        Box::new(PolyExpr::Add(
                            Box::new(PolyExpr::StateVar("B".into())),
                            Box::new(PolyExpr::StateVar("C".into())),
                        )),
                    ),
                ),
                (
                    "C".into(),
                    PolyExpr::Neg(Box::new(PolyExpr::StateVar("B".into()))),
                ),
            ],
            atomic_ops: vec![AtomicOpCompareSpec {
                name: "apply".into(),
                arg_vars: vec!["u".into()],
                before_updates: vec![
                    (
                        "B".into(),
                        PolyExpr::Add(
                            Box::new(PolyExpr::StateVar("B".into())),
                            Box::new(PolyExpr::ArgVar("u".into())),
                        ),
                    ),
                    ("C".into(), PolyExpr::StateVar("C".into())),
                ],
                after_updates: vec![
                    (
                        "B".into(),
                        PolyExpr::Add(
                            Box::new(PolyExpr::StateVar("B".into())),
                            Box::new(PolyExpr::Mul(
                                Box::new(PolyExpr::Const(ScalarLit::Z(BigInt::from(2)))),
                                Box::new(PolyExpr::ArgVar("u".into())),
                            )),
                        ),
                    ),
                    (
                        "C".into(),
                        PolyExpr::Sub(
                            Box::new(PolyExpr::StateVar("C".into())),
                            Box::new(PolyExpr::ArgVar("u".into())),
                        ),
                    ),
                ],
            }],
            extended_checks: vec![ExtendedOperationCheckSpec::RuntimeArgOp {
                name: "compact_all".into(),
                before_updates: vec![
                    (
                        "B".into(),
                        PolyExpr::Add(
                            Box::new(PolyExpr::StateVar("B".into())),
                            Box::new(PolyExpr::StateVar("C".into())),
                        ),
                    ),
                    ("C".into(), PolyExpr::Const(ScalarLit::Z(BigInt::from(0)))),
                ],
                after_updates: vec![
                    (
                        "B".into(),
                        PolyExpr::Add(
                            Box::new(PolyExpr::StateVar("B".into())),
                            Box::new(PolyExpr::StateVar("C".into())),
                        ),
                    ),
                    ("C".into(), PolyExpr::Const(ScalarLit::Z(BigInt::from(0)))),
                ],
                sample_state: vec![
                    ("B".into(), PolyExpr::Const(ScalarLit::Z(BigInt::from(1)))),
                    ("C".into(), PolyExpr::Const(ScalarLit::Z(BigInt::from(0)))),
                ],
            }],
        }),
        provenance: sample_prov(),
    };
    assert!(validate_atlas_task(valid.clone()).is_ok());

    let mut self_loop = valid.clone();
    self_loop.edges[0].to = "v0".into();
    assert!(matches!(
        validate_atlas_task(self_loop),
        Err(ValidationError::ConversionError { .. })
    ));

    // refinement の nerve_edge_map が欠落している場合は拒否
    let mut bad_ref = valid;
    let dummy_nerve = SupportedNerveSpec {
        charts: vec![
            ChartSupportSpec {
                name: "c0".into(),
                support: vec!["s0".into()],
            },
            ChartSupportSpec {
                name: "c1".into(),
                support: vec!["s0".into()],
            },
        ],
        edges: vec![NerveEdgeSpec {
            name: "ne0".into(),
            left: "c0".into(),
            right: "c1".into(),
        }],
        faces: vec![],
    };
    bad_ref.refinement = Some(AtlasRefinementSpec {
        fine_vertices: vec!["v0".into(), "v1".into(), "v2".into()],
        fine_edges: bad_ref.edges.clone(),
        vertex_map: vec![
            ("v0".into(), "v0".into()),
            ("v1".into(), "v1".into()),
            ("v2".into(), "v2".into()),
        ],
        edge_map: vec![
            ("e01".into(), Some("e01".into())),
            ("e12".into(), Some("e12".into())),
            ("e20".into(), Some("e20".into())),
        ],
        common_sources: vec!["s0".into()],
        coarse_reading: vec![("s0".into(), "s0".into())],
        fine_reading: vec![("s0".into(), "s0".into())],
        coarse_nerve: dummy_nerve.clone(),
        fine_nerve: dummy_nerve,
        nerve_chart_map: vec![("c0".into(), "c0".into()), ("c1".into(), "c1".into())],
        nerve_edge_map: vec![], // ne0 欠落
        nerve_face_map: vec![],
        eval_condition: None,
        forgetful_reading: None,
    });
    assert!(matches!(
        validate_atlas_task(bad_ref),
        Err(ValidationError::ConversionError { .. })
    ));
}

#[test]
fn phase4_outcome_details_and_silence_serialize_cleanly() {
    let empty_repair = ConstrainedRepairSummary {
        allowed_items: vec![],
        repair_exists: false,
        particular_delta: None,
        torsor_basis: vec![],
        h0_operation_torsor_rank: 0,
        reevaluation: None,
    };
    let outcome = ShigureOutcome {
        verdict: Verdict::Undetermined(SilenceReason::NonNoetherianInfinitePresentation {
            detail: "T_i = T_{i+1}^2 is non-Noetherian".into(),
        }),
        coeff_domain: CoeffDomain::Q,
        point_domain: PointDomain::AlgebraicClosure,
        applicability: vec![],
        provenance: sample_prov(),
        residual_ideal: vec![],
        empty_witness: None,
        restored: None,
        interaction: None,
        diagram: None,
        path: None,
        transfer: None,
        robustness: None,
        chevalley: None,
        observations: None,
        lift: Some(LiftOutcomeDetail {
            coeff_ring_label: "Q".into(),
            r_base_label: "Q[eps]/(eps^2)".into(),
            r_prime_label: "Q[eps]/(eps^3)".into(),
            kernel_dim: 1,
            square_zero_verified: true,
            base_point_lawful: true,
            syzygy_generators: vec![],
            syzygy_identity_verified: true,
            complex_d1_d0_zero_verified: true,
            residual_cocycle_verified: true,
            residual_in_m: vec!["1".into()],
            h0_dim: 1,
            h1_dim: 1,
            h0_basis: vec![],
            obstruction_class_coords: vec!["1".into()],
            obstruction_is_zero: false,
            lift_exists: false,
            restored_lift: None,
            reevaluation: None,
            raw_cech_comparison: None,
            relative_cone: None,
            declaration_cover: None,
            affine_repair: None,
            redundant_comparison: None,
            etale_descent: None,
        }),
        artin: Some(ArtinOutcomeDetail {
            test_ring_family: "all_local_artin_algebras_universal_quotient".into(),
            is_free_observation_chart: true,
            eliminated_residuals: vec!["t^2".into()],
            syntactic_degree_bound: Some(2),
            detection_order_nu: Some(2),
            local_isomorphism_at_base: false,
            lift_failure_mode: "nu_ge_2_realization_unliftable".into(),
            universal_first_obstruction: None,
            composition_law: None,
            base_change: None,
        }),
        diagnostics: Some(DiagnosticsOutcomeDetail {
            diagnostic_coeff_label: "Z".into(),
            reading_adequate: true,
            d1_d0_zero_verified: true,
            cell_dims: [3, 3, 0],
            h0_summary: "Z".into(),
            h1_summary: "Z".into(),
            h2_summary: "0".into(),
            h0_free_rank: 1,
            h1_free_rank: 1,
            h1_torsion: vec![],
            h2_free_rank: 0,
            block_decomposition: vec![],
            coeff_change: None,
            strata: vec![],
            collisions: vec![],
            upper_semicontinuity_refutation: None,
            r_point_contrast: None,
            dimension_realization: None,
        }),
        atlas: Some(AtlasOutcomeDetail {
            coeff_ring_label: "Z".into(),
            num_vertices: 3,
            num_edges: 3,
            graph_connected: true,
            saga_sign_commutes_verified: true,
            real_residuals: BTreeMap::new(),
            spanning_tree_edges: vec!["e01".into(), "e12".into()],
            chord_edges: vec!["e20".into()],
            designated_class_o_b_coords: vec!["0".into()],
            designated_class_kappa_b_coords: vec!["0".into()],
            o_b_is_zero: true,
            kappa_b_is_zero: true,
            diagnostic_h1_rank: 1,
            primitive_relation_connected_verified: true,
            z_to_q_zero_reflection_verified: Some(true),
            unconstrained_global_operation_exists: true,
            unconstrained_particular_lambda: None,
            unconstrained_h0_torsor_rank: 1,
            unconstrained_reevaluation: None,
            vertex_constrained_repair: empty_repair.clone(),
            edge_constrained_repair: empty_repair,
            refinement: None,
            extended_language_non_transport: Some(ExtendedLanguageResult {
                atomic_ops_commute: BTreeMap::from([("apply".into(), true)]),
                all_atomic_ops_commute: true,
                extended_check_results: vec![ExtendedCheckOutcome {
                    name: "compact_all".into(),
                    kind: "runtime_arg_op".into(),
                    transport_preserved: false,
                    before_values: vec!["2".into(), "-1".into()],
                    after_values: vec!["1".into(), "0".into()],
                    law_residuals: vec![],
                    detail: "g(op(x)) != op(g(x))".into(),
                }],
                all_extended_checks_preserved: false,
            }),
        }),
    };
    let json = outcome.to_json();
    let Json::Obj(ref map) = json else {
        panic!("expected Json::Obj");
    };
    assert!(map.contains_key("lift"));
    assert!(map.contains_key("artin"));
    assert!(map.contains_key("diagnostics"));
    assert!(map.contains_key("atlas"));
    let Some(Json::Obj(sr)) = map.get("silence_reason") else {
        panic!("expected silence_reason object");
    };
    assert_eq!(
        sr.get("code"),
        Some(&Json::str("non_noetherian_infinite_presentation"))
    );
}

#[test]
fn phase4_ir_rejects_bad_literals_unobserved_provenance_and_edge_cases() {
    use num_bigint::BigUint;

    // 1. PolyExpr::Const 分母 0 / 不正 Fp / ドメイン不一致・Unobserved 空 slot / 逆転 span・NamedPoly.provenance 不正を拒否
    let base_artin = || ArtinTaskSpec {
        name: "bad_lit_check".into(),
        coeff_domain: CoeffDomain::Q,
        obs_vars: vec!["x".into()],
        obs_relations: vec![],
        aux_defs: vec![],
        extra_laws: vec![NamedPoly {
            name: "l0".into(),
            expr: PolyExpr::StateVar("x".into()),
            provenance: None,
        }],
        base_point: vec![("x".into(), PolyExpr::Const(ScalarLit::Z(BigInt::from(0))))],
        max_order: 2,
        max_artin_dim: None,
        composite_stage: None,
        base_change: None,
        non_noetherian_infinite: false,
        provenance: sample_prov(),
    };

    let mut bad_q = base_artin();
    bad_q.extra_laws[0].expr = PolyExpr::Const(ScalarLit::Q {
        num: BigInt::from(1),
        den: BigInt::from(0),
    });
    assert!(matches!(
        validate_artin_task(bad_q),
        Err(ValidationError::InvalidRational { .. })
    ));

    let mut bad_fp = base_artin();
    bad_fp.extra_laws[0].expr = PolyExpr::Const(ScalarLit::Fp {
        value: BigUint::from(99u32),
        modulus: BigUint::from(4u32),
    });
    assert!(matches!(
        validate_artin_task(bad_fp),
        Err(ValidationError::DomainMismatch { .. })
    ));

    let mut bad_unobs_slot = base_artin();
    bad_unobs_slot.base_point[0].1 = PolyExpr::Unobserved {
        slot: "   ".into(),
        origin: None,
    };
    assert!(matches!(
        validate_artin_task(bad_unobs_slot),
        Err(ValidationError::EmptyName { .. })
    ));

    let mut bad_unobs_span = base_artin();
    let mut bad_sr = SourceRef::new("phase4:test", OriginKind::HumanAdopted);
    bad_sr.span = Some((10, 2));
    bad_unobs_span.base_point[0].1 = PolyExpr::Unobserved {
        slot: "missing_val".into(),
        origin: Some(bad_sr.clone()),
    };
    assert!(matches!(
        validate_artin_task(bad_unobs_span),
        Err(ValidationError::InvalidSourceSpan { .. })
    ));

    let mut bad_named_prov = base_artin();
    bad_named_prov.extra_laws[0].provenance = Some(bad_sr);
    assert!(matches!(
        validate_artin_task(bad_named_prov),
        Err(ValidationError::InvalidSourceSpan { .. })
    ));

    // 2. Lift: obs_vars と ring_params の名前衝突・two_context_cech.shared_vars が両文脈に属さない場合を拒否
    let base_lift = || LiftTaskSpec {
        name: "lift_edge".into(),
        coeff_domain: CoeffDomain::Q,
        variables: vec!["x".into(), "y".into()],
        ring_params: vec![RingParamSpec {
            name: "eps".into(),
            value_in_r_prime: vec![
                PolyExpr::Const(ScalarLit::Z(BigInt::from(0))),
                PolyExpr::Const(ScalarLit::Z(BigInt::from(1))),
            ],
        }],
        laws: vec![NamedPoly {
            name: "l1".into(),
            expr: PolyExpr::StateVar("x".into()),
            provenance: None,
        }],
        extension: SquareZeroSpec::TruncatedPoly {
            var_name: "eps".into(),
            base_degree: 0,
        },
        base_point: vec![
            ("x".into(), vec![PolyExpr::Const(ScalarLit::Z(BigInt::from(0)))]),
            ("y".into(), vec![PolyExpr::Const(ScalarLit::Z(BigInt::from(0)))]),
        ],
        ambient_lift: None,
        relative_reading: None,
        declaration_cover: None,
        affine_allowed: None,
        redundant_comparison: None,
        etale_descent: None,
        max_syzygy_pairs: None,
        provenance: sample_prov(),
    };

    let mut obs_param_clash = base_lift();
    obs_param_clash.relative_reading = Some(RelativeReadingSpec {
        obs_vars: vec!["eps".into()],
        obs_laws: vec![],
        reading_map: vec![("eps".into(), PolyExpr::StateVar("x".into()))],
        designated_obs_lift: vec![(
            "eps".into(),
            vec![
                PolyExpr::Const(ScalarLit::Z(BigInt::from(0))),
                PolyExpr::Const(ScalarLit::Z(BigInt::from(0))),
            ],
        )],
        raw_read_diff: None,
    });
    assert!(matches!(
        validate_lift_task(obs_param_clash),
        Err(ValidationError::DuplicateDecl {
            kind: "obs_var",
            ..
        })
    ));

    let mut bad_shared = base_lift();
    bad_shared.declaration_cover = Some(DeclarationCoverSpec {
        contexts: vec![
            DeclarationContextSpec {
                name: "left".into(),
                vars: vec!["x".into()],
                laws: vec!["l1".into()],
                observations: vec![],
            },
            DeclarationContextSpec {
                name: "right".into(),
                vars: vec!["y".into()],
                laws: vec![],
                observations: vec![],
            },
        ],
        two_context_cech: Some(TwoContextCechSpec {
            left_context: "left".into(),
            right_context: "right".into(),
            shared_vars: vec!["x".into()],
        }),
    });
    assert!(matches!(
        validate_lift_task(bad_shared),
        Err(ValidationError::UnknownRef {
            kind: "variable",
            ..
        })
    ));

    // 3. Diagnostics: Static law 内ドメイン混在・chart.support 重複・collisions 重複 label を拒否
    let base_diag = || DiagnosticsTaskSpec {
        name: "diag_edge".into(),
        diagnostic_coeff: CoeffDomain::Z,
        readout: DiagnosticsReadoutSpec::Static {
            sources: vec!["s0".into(), "s1".into()],
            targets: vec!["s0".into(), "s1".into()],
            reading: vec![("s0".into(), "s0".into()), ("s1".into(), "s1".into())],
            laws: vec![StaticLawReadoutSpec {
                law_name: "L".into(),
                values: vec![
                    ("s0".into(), ScalarLit::Z(BigInt::from(0))),
                    ("s1".into(), ScalarLit::Z(BigInt::from(1))),
                ],
            }],
        },
        nerve: SupportedNerveSpec {
            charts: vec![ChartSupportSpec {
                name: "c0".into(),
                support: vec!["s0".into(), "s1".into()],
            }],
            edges: vec![],
            faces: vec![],
        },
        coeff_change: None,
        collisions: vec![],
        r_point_probe: None,
        dimension_realization: None,
        max_partitions: None,
        provenance: sample_prov(),
    };

    let mut mixed_dom = base_diag();
    if let DiagnosticsReadoutSpec::Static { ref mut laws, .. } = mixed_dom.readout {
        laws[0].values[1].1 = ScalarLit::Q {
            num: BigInt::from(1),
            den: BigInt::from(1),
        };
    }
    assert!(matches!(
        validate_diagnostics_task(mixed_dom),
        Err(ValidationError::DomainMismatch { .. })
    ));

    let mut dup_sup = base_diag();
    dup_sup.nerve.charts[0].support.push("s0".into());
    assert!(matches!(
        validate_diagnostics_task(dup_sup),
        Err(ValidationError::DuplicateDecl {
            kind: "nerve_chart_support",
            ..
        })
    ));

    let mut dup_col = base_diag();
    let col_item = CollisionComparisonSpec {
        label: "dup".into(),
        law_name: "L".into(),
        fine_partition: vec![vec!["s0".into()], vec!["s1".into()]],
        coarse_partition: vec![vec!["s0".into(), "s1".into()]],
        alternative_merge_paths: vec![],
    };
    dup_col.collisions = vec![col_item.clone(), col_item];
    assert!(matches!(
        validate_diagnostics_task(dup_col),
        Err(ValidationError::DuplicateDecl {
            kind: "collision",
            ..
        })
    ));

    // 4. Atlas: common_sources 空名・reading target 空名・intermediate_laws 重複名を拒否
    let dummy_nerve = SupportedNerveSpec {
        charts: vec![ChartSupportSpec {
            name: "c0".into(),
            support: vec!["t0".into()],
        }],
        edges: vec![],
        faces: vec![],
    };
    let mut bad_atlas = AtlasTaskSpec {
        name: "atlas_edge".into(),
        coeff_domain: CoeffDomain::Z,
        compare_to_q: false,
        vertices: vec!["v0".into(), "v1".into()],
        edges: vec![GraphEdgeSpec {
            name: "e0".into(),
            from: "v0".into(),
            to: "v1".into(),
            offset: PolyExpr::Const(ScalarLit::Z(BigInt::from(0))),
        }],
        mu: PolyExpr::Const(ScalarLit::Z(BigInt::from(1))),
        base_lambdas: vec![
            ("v0".into(), PolyExpr::Const(ScalarLit::Z(BigInt::from(0)))),
            ("v1".into(), PolyExpr::Const(ScalarLit::Z(BigInt::from(0)))),
        ],
        allowed_vertices: vec![],
        allowed_edges: vec![],
        refinement: Some(AtlasRefinementSpec {
            fine_vertices: vec!["v0".into(), "v1".into()],
            fine_edges: vec![GraphEdgeSpec {
                name: "e0".into(),
                from: "v0".into(),
                to: "v1".into(),
                offset: PolyExpr::Const(ScalarLit::Z(BigInt::from(0))),
            }],
            vertex_map: vec![("v0".into(), "v0".into()), ("v1".into(), "v1".into())],
            edge_map: vec![("e0".into(), Some("e0".into()))],
            common_sources: vec!["  ".into()],
            coarse_reading: vec![("  ".into(), "t0".into())],
            fine_reading: vec![("  ".into(), "t0".into())],
            coarse_nerve: dummy_nerve.clone(),
            fine_nerve: dummy_nerve.clone(),
            nerve_chart_map: vec![("c0".into(), "c0".into())],
            nerve_edge_map: vec![],
            nerve_face_map: vec![],
            eval_condition: None,
            forgetful_reading: None,
        }),
        extended_language_check: None,
        provenance: sample_prov(),
    };
    assert!(matches!(
        validate_atlas_task(bad_atlas.clone()),
        Err(ValidationError::EmptyName { .. })
    ));

    if let Some(ref mut r) = bad_atlas.refinement {
        r.common_sources = vec!["s0".into()];
        r.coarse_reading = vec![("s0".into(), "".into())];
        r.fine_reading = vec![("s0".into(), "t0".into())];
    }
    assert!(matches!(
        validate_atlas_task(bad_atlas.clone()),
        Err(ValidationError::EmptyName { .. })
    ));

    bad_atlas.refinement = None;
    bad_atlas.extended_language_check = Some(ExtendedLanguageCheckSpec {
        state_vars: vec!["s".into()],
        adapter_map: vec![("s".into(), PolyExpr::StateVar("s".into()))],
        atomic_ops: vec![],
        extended_checks: vec![ExtendedOperationCheckSpec::ProtocolSequence {
            name: "p".into(),
            extended_state_vars: vec!["s".into()],
            initial_state: vec![("s".into(), PolyExpr::Const(ScalarLit::Z(BigInt::from(0))))],
            before_steps: vec![],
            after_steps: vec![],
            before_read: Box::new(PolyExpr::StateVar("s".into())),
            after_read: Box::new(PolyExpr::StateVar("s".into())),
            intermediate_laws: vec![
                NamedPoly {
                    name: "dup_il".into(),
                    expr: PolyExpr::StateVar("s".into()),
                    provenance: None,
                },
                NamedPoly {
                    name: "dup_il".into(),
                    expr: PolyExpr::StateVar("s".into()),
                    provenance: None,
                },
            ],
        }],
    });
    assert!(matches!(
        validate_atlas_task(bad_atlas),
        Err(ValidationError::DuplicateDecl {
            kind: "intermediate_law",
            ..
        })
    ));
}
