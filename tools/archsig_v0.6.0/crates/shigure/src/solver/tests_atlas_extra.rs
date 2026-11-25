//! `solver/atlas*` の E3 nerve-graph 整合回帰テスト（Round 3 監査対応）。

use crate::ir::atlas::{AtlasRefinementSpec, AtlasTaskSpec, GraphEdgeSpec, validate_atlas_task};
use crate::ir::diagnostics::{ChartSupportSpec, NerveEdgeSpec, SupportedNerveSpec};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::Verdict;
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::solver::solve_atlas_task;

fn q(n: i64) -> PolyExpr {
    PolyExpr::Const(ScalarLit::rat(n, 1).unwrap())
}

fn prov() -> Provenance {
    Provenance::new(
        vec![SourceRef::new("test_atlas_extra", OriginKind::HumanAdopted)],
        vec![MathClause::G142E3, MathClause::G142F4],
    )
}

fn base_triangle_task(refinement: AtlasRefinementSpec) -> AtlasTaskSpec {
    AtlasTaskSpec {
        name: "e3_alignment_check".into(),
        coeff_domain: CoeffDomain::Q,
        vertices: vec!["v0".into(), "v1".into(), "v2".into()],
        edges: vec![
            GraphEdgeSpec {
                name: "e01".into(),
                from: "v0".into(),
                to: "v1".into(),
                offset: q(1),
            },
            GraphEdgeSpec {
                name: "e12".into(),
                from: "v1".into(),
                to: "v2".into(),
                offset: q(2),
            },
            GraphEdgeSpec {
                name: "e20".into(),
                from: "v2".into(),
                to: "v0".into(),
                offset: q(-3),
            },
        ],
        mu: q(1),
        base_lambdas: vec![("v0".into(), q(0)), ("v1".into(), q(0)), ("v2".into(), q(0))],
        allowed_vertices: vec!["v0".into(), "v1".into(), "v2".into()],
        allowed_edges: Vec::new(),
        compare_to_q: false,
        refinement: Some(refinement),
        extended_language_check: None,
        provenance: prov(),
    }
}

type FineGraphData = (
    Vec<String>,
    Vec<GraphEdgeSpec>,
    Vec<(String, String)>,
    Vec<(String, Option<String>)>,
);

fn w3_fine_graph() -> FineGraphData {
    (
        vec!["v0a".into(), "v0b".into(), "v1".into(), "v2".into()],
        vec![
            GraphEdgeSpec {
                name: "t".into(),
                from: "v0a".into(),
                to: "v0b".into(),
                offset: q(0),
            },
            GraphEdgeSpec {
                name: "e01".into(),
                from: "v0b".into(),
                to: "v1".into(),
                offset: q(1),
            },
            GraphEdgeSpec {
                name: "e12".into(),
                from: "v1".into(),
                to: "v2".into(),
                offset: q(2),
            },
            GraphEdgeSpec {
                name: "e20".into(),
                from: "v2".into(),
                to: "v0a".into(),
                offset: q(-3),
            },
        ],
        vec![
            ("v0a".into(), "v0".into()),
            ("v0b".into(), "v0".into()),
            ("v1".into(), "v1".into()),
            ("v2".into(), "v2".into()),
        ],
        vec![
            ("t".into(), None),
            ("e01".into(), Some("e01".into())),
            ("e12".into(), Some("e12".into())),
            ("e20".into(), Some("e20".into())),
        ],
    )
}

#[test]
fn e3_unaligned_trivial_or_empty_edge_nerve_rejects_designated_kappa_preserved() {
    let (fv, fe, vm, em) = w3_fine_graph();

    // 反例 A: 1-chart 0-edge の自明 nerve は C0–C6 自体を通るが、グラフとの E3 整合を欠くため
    // designated_kappa_preserved == false かつ Verdict::Refuted となる。
    let trivial_ref = AtlasRefinementSpec {
        fine_vertices: fv.clone(),
        fine_edges: fe.clone(),
        vertex_map: vm.clone(),
        edge_map: em.clone(),
        common_sources: vec!["s0".into()],
        coarse_reading: vec![("s0".into(), "s0".into())],
        fine_reading: vec![("s0".into(), "s0".into())],
        coarse_nerve: SupportedNerveSpec {
            charts: vec![ChartSupportSpec {
                name: "only".into(),
                support: vec!["s0".into()],
            }],
            edges: Vec::new(),
            faces: Vec::new(),
        },
        fine_nerve: SupportedNerveSpec {
            charts: vec![ChartSupportSpec {
                name: "only_f".into(),
                support: vec!["s0".into()],
            }],
            edges: Vec::new(),
            faces: Vec::new(),
        },
        nerve_chart_map: vec![("only_f".into(), "only".into())],
        nerve_edge_map: Vec::new(),
        nerve_face_map: Vec::new(),
        eval_condition: None,
        forgetful_reading: None,
    };
    let out_a = solve_atlas_task(&validate_atlas_task(base_triangle_task(trivial_ref)).unwrap());
    assert_eq!(out_a.verdict, Verdict::Refuted);
    let ra = out_a.atlas.unwrap().refinement.unwrap();
    assert!(ra.condition_c.all_passed);
    assert!(ra.designated_o_preserved);
    assert!(!ra.designated_kappa_preserved);

    // 反例 B: 頂点・辺名は一致するが chart 支持が互いに素で全辺支持が空 -> C^1(nerve) = 0 で E3 不整合。
    let disjoint_ref = AtlasRefinementSpec {
        fine_vertices: fv,
        fine_edges: fe,
        vertex_map: vm.clone(),
        edge_map: em.clone(),
        common_sources: vec!["s0".into(), "s1".into(), "s2".into()],
        coarse_reading: vec![
            ("s0".into(), "s0".into()),
            ("s1".into(), "s1".into()),
            ("s2".into(), "s2".into()),
        ],
        fine_reading: vec![
            ("s0".into(), "s0".into()),
            ("s1".into(), "s1".into()),
            ("s2".into(), "s2".into()),
        ],
        coarse_nerve: SupportedNerveSpec {
            charts: vec![
                ChartSupportSpec {
                    name: "v0".into(),
                    support: vec!["s0".into()],
                },
                ChartSupportSpec {
                    name: "v1".into(),
                    support: vec!["s1".into()],
                },
                ChartSupportSpec {
                    name: "v2".into(),
                    support: vec!["s2".into()],
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
                    support: vec!["s0".into()],
                },
                ChartSupportSpec {
                    name: "v0b".into(),
                    support: vec!["s0".into()],
                },
                ChartSupportSpec {
                    name: "v1".into(),
                    support: vec!["s1".into()],
                },
                ChartSupportSpec {
                    name: "v2".into(),
                    support: vec!["s2".into()],
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
        nerve_chart_map: vm,
        nerve_edge_map: em,
        nerve_face_map: Vec::new(),
        eval_condition: None,
        forgetful_reading: None,
    };
    let out_b = solve_atlas_task(&validate_atlas_task(base_triangle_task(disjoint_ref)).unwrap());
    assert_eq!(out_b.verdict, Verdict::Refuted);
    let rb = out_b.atlas.unwrap().refinement.unwrap();
    assert!(rb.condition_c.all_passed);
    assert!(!rb.designated_kappa_preserved);
}
