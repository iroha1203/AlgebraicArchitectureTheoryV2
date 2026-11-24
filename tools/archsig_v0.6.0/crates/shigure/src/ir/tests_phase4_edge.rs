//! Phase 4 IR のエッジケース検証（リテラル・Unobserved・NamedPoly.provenance・3 名前空間分離・上限検査）単体テスト（AC1）。

use crate::ir::artin::{ArtinTaskSpec, validate_artin_task};
use crate::ir::atlas::{
    AtlasEvalConditionSpec, AtlasRefinementSpec, AtlasTaskSpec, AtomicOpCompareSpec,
    ExtendedLanguageCheckSpec, ExtendedOperationCheckSpec, GraphEdgeSpec, validate_atlas_task,
};
use crate::ir::change::NamedPoly;
use crate::ir::diagnostics::{
    ChartSupportSpec, CollisionComparisonSpec, DiagnosticsReadoutSpec, DiagnosticsTaskSpec,
    StaticLawReadoutSpec, SupportedNerveSpec, validate_diagnostics_task,
};
use crate::ir::lift::{
    DeclarationContextSpec, DeclarationCoverSpec, LiftTaskSpec, RelativeReadingSpec, RingParamSpec,
    SquareZeroSpec, TwoContextCechSpec, validate_lift_task,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::ir::validate::ValidationError;
use num_bigint::{BigInt, BigUint};

fn sample_prov() -> Provenance {
    Provenance::new(
        vec![SourceRef::new("phase4:edge", OriginKind::HumanAdopted)],
        vec![MathClause::G141E2],
    )
}

#[test]
fn phase4_ir_rejects_bad_literals_unobserved_provenance_and_edge_cases() {
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
        validate_atlas_task(bad_atlas.clone()),
        Err(ValidationError::DuplicateDecl {
            kind: "intermediate_law",
            ..
        })
    ));

    // 5. 3 名前空間分離検査（StateVar / ArgVar / ParamVar 取り違えを拒否）および eval_condition 頂点/辺名衝突拒否
    let mut ns_clash = base_lift();
    ns_clash.laws[0].expr = PolyExpr::StateVar("eps".into());
    assert!(matches!(
        validate_lift_task(ns_clash.clone()),
        Err(ValidationError::UnknownRef {
            kind: "state coordinate",
            ..
        })
    ));
    ns_clash.laws[0].expr = PolyExpr::ParamVar("eps".into());
    assert!(validate_lift_task(ns_clash.clone()).is_ok());
    ns_clash.laws[0].expr = PolyExpr::ParamVar("x".into());
    assert!(matches!(
        validate_lift_task(ns_clash.clone()),
        Err(ValidationError::UnknownRef {
            kind: "parameter",
            ..
        })
    ));
    ns_clash.laws[0].expr = PolyExpr::StateVar("x".into());
    ns_clash.extension = SquareZeroSpec::TruncatedPoly {
        var_name: "eps".into(),
        base_degree: usize::MAX,
    };
    assert!(matches!(
        validate_lift_task(ns_clash),
        Err(ValidationError::ConversionError { .. })
    ));

    let mut bad_atomic = bad_atlas;
    bad_atomic.extended_language_check = Some(ExtendedLanguageCheckSpec {
        state_vars: vec!["s".into()],
        adapter_map: vec![("s".into(), PolyExpr::StateVar("s".into()))],
        atomic_ops: vec![AtomicOpCompareSpec {
            name: "op".into(),
            arg_vars: vec!["u".into()],
            before_updates: vec![("s".into(), PolyExpr::StateVar("u".into()))],
            after_updates: vec![("s".into(), PolyExpr::ArgVar("u".into()))],
        }],
        extended_checks: vec![],
    });
    assert!(matches!(
        validate_atlas_task(bad_atomic),
        Err(ValidationError::UnknownRef {
            kind: "state coordinate",
            ..
        })
    ));

    let clash_atlas = AtlasTaskSpec {
        name: "ve_clash".into(),
        coeff_domain: CoeffDomain::Z,
        compare_to_q: false,
        vertices: vec!["x".into(), "y".into()],
        edges: vec![GraphEdgeSpec {
            name: "x".into(),
            from: "x".into(),
            to: "y".into(),
            offset: PolyExpr::Const(ScalarLit::Z(BigInt::from(0))),
        }],
        mu: PolyExpr::Const(ScalarLit::Z(BigInt::from(1))),
        base_lambdas: vec![
            ("x".into(), PolyExpr::Const(ScalarLit::Z(BigInt::from(0)))),
            ("y".into(), PolyExpr::Const(ScalarLit::Z(BigInt::from(0)))),
        ],
        allowed_vertices: vec![],
        allowed_edges: vec![],
        refinement: Some(AtlasRefinementSpec {
            fine_vertices: vec!["x".into(), "y".into()],
            fine_edges: vec![GraphEdgeSpec {
                name: "x".into(),
                from: "x".into(),
                to: "y".into(),
                offset: PolyExpr::Const(ScalarLit::Z(BigInt::from(0))),
            }],
            vertex_map: vec![("x".into(), "x".into()), ("y".into(), "y".into())],
            edge_map: vec![("x".into(), Some("x".into()))],
            common_sources: vec!["s0".into()],
            coarse_reading: vec![("s0".into(), "t0".into())],
            fine_reading: vec![("s0".into(), "t0".into())],
            coarse_nerve: dummy_nerve.clone(),
            fine_nerve: dummy_nerve,
            nerve_chart_map: vec![("c0".into(), "c0".into())],
            nerve_edge_map: vec![],
            nerve_face_map: vec![],
            eval_condition: Some(AtlasEvalConditionSpec {
                evaluations: vec![],
                equations: vec![],
                invertibles: vec![],
            }),
            forgetful_reading: None,
        }),
        extended_language_check: None,
        provenance: sample_prov(),
    };
    assert!(matches!(
        validate_atlas_task(clash_atlas),
        Err(ValidationError::DuplicateDecl {
            kind: "eval_condition_var",
            ..
        })
    ));
}
