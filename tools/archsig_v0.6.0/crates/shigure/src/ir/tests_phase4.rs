//! Phase 4 IR（`lift`・`artin`・`diagnostics`・`atlas`・`result_phase4`）の構築・検証・JSON 出力単体テスト（AC1）。

use crate::ir::artin::{ArtinTaskSpec, AuxiliaryDefSpec, validate_artin_task};
use crate::ir::atlas::{AtlasTaskSpec, GraphEdgeSpec, validate_atlas_task};
use crate::ir::change::{NamedPoly, PointDomain};
use crate::ir::diagnostics::{
    ChartSupportSpec, DiagnosticsReadoutSpec, DiagnosticsTaskSpec, NerveEdgeSpec, NerveFaceSpec,
    StaticLawReadoutSpec, SupportedNerveSpec, validate_diagnostics_task,
};
use crate::ir::lift::{LiftTaskSpec, SquareZeroSpec, validate_lift_task};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{ShigureOutcome, SilenceReason, Verdict};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::ir::validate::ValidationError;
use num_bigint::BigInt;

fn sample_prov() -> Provenance {
    Provenance::new(
        vec![SourceRef::new("phase4:test", OriginKind::HumanAdopted)],
        vec![MathClause::G141E2],
    )
}

#[test]
fn lift_task_validation_accepts_valid_and_rejects_bad_dimension() {
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

    let mut bad = valid;
    bad.base_point[0].1.pop();
    assert!(matches!(
        validate_lift_task(bad),
        Err(ValidationError::ConversionError { .. })
    ));
}

#[test]
fn artin_task_validation_enforces_acyclic_aux_dependency_order() {
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
        composite_stage: None,
        base_change: None,
        non_noetherian_infinite: false,
        provenance: sample_prov(),
    };
    let checked = validate_artin_task(valid.clone()).unwrap();
    assert!(checked.is_free_observation_chart());

    // 循環・逆順参照（y1 がまだ未定義の y2 を参照）は拒否される
    let mut cyclic = valid;
    cyclic.aux_defs[0].expr = PolyExpr::StateVar("y2".into());
    assert!(matches!(
        validate_artin_task(cyclic),
        Err(ValidationError::UnknownRef { .. })
    ));
}

#[test]
fn diagnostics_task_validation_enforces_k1_face_endpoint_equations() {
    let nerve_ok = SupportedNerveSpec {
        charts: vec![
            ChartSupportSpec {
                name: "c0".into(),
                support: vec!["s0".into()],
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
    let make_spec = |nerve: SupportedNerveSpec| DiagnosticsTaskSpec {
        name: "k1_check".into(),
        diagnostic_coeff: CoeffDomain::Z,
        nerve,
        readout: DiagnosticsReadoutSpec::Static {
            sources: vec!["s0".into()],
            targets: vec!["s0".into()],
            reading: vec![("s0".into(), "s0".into())],
            laws: vec![StaticLawReadoutSpec {
                law_name: "L".into(),
                values: vec![("s0".into(), ScalarLit::Z(BigInt::from(0)))],
            }],
        },
        coeff_change: None,
        collisions: vec![],
        r_point_probe: None,
        dimension_realization: None,
        max_partitions: None,
        provenance: sample_prov(),
    };
    assert!(validate_diagnostics_task(make_spec(nerve_ok.clone())).is_ok());

    // e1 と e2 を入れ替えると K1 端点等式 r(e0) == l(e2) が破れるため拒否される
    let mut nerve_bad = nerve_ok;
    nerve_bad.faces[0].e1 = "e12".into();
    nerve_bad.faces[0].e2 = "e02".into();
    assert!(matches!(
        validate_diagnostics_task(make_spec(nerve_bad)),
        Err(ValidationError::ConversionError { .. })
    ));
}

#[test]
fn atlas_task_validation_enforces_simple_graph_without_self_loops_or_parallel_edges() {
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
        extended_language_check: None,
        provenance: sample_prov(),
    };
    assert!(validate_atlas_task(valid.clone()).is_ok());

    let mut self_loop = valid.clone();
    self_loop.edges[0].to = "v0".into();
    assert!(matches!(
        validate_atlas_task(self_loop),
        Err(ValidationError::ConversionError { .. })
    ));

    let mut parallel = valid;
    parallel.edges.push(GraphEdgeSpec {
        name: "e10_dup".into(),
        from: "v1".into(),
        to: "v0".into(),
        offset: PolyExpr::Const(ScalarLit::Z(BigInt::from(0))),
    });
    assert!(matches!(
        validate_atlas_task(parallel),
        Err(ValidationError::ConversionError { .. })
    ));
}

#[test]
fn phase4_silence_reason_codes_serialize_cleanly() {
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
        lift: None,
        artin: None,
        diagnostics: None,
        atlas: None,
    };
    let json = outcome.to_json();
    let archsig_common::canonical::Json::Obj(map) = &json else {
        panic!("expected Json::Obj");
    };
    let Some(archsig_common::canonical::Json::Obj(sr)) = map.get("silence_reason") else {
        panic!("expected silence_reason object");
    };
    assert_eq!(
        sr.get("code"),
        Some(&archsig_common::canonical::Json::str(
            "non_noetherian_infinite_presentation"
        ))
    );
}
