use crate::ir::change::{ChangeSpec, EditableTarget, FixedTarget, ParamDecl};
use crate::ir::diagram::{
    CheckedDiagramTask, DiagramEdge, DiagramRelation, DiagramSpec, DiagramVertex,
};
use crate::ir::morphism::{MorphismDirection, StateMorphism};
use crate::ir::presentation::{
    CoordDecl, ObservationDecl, OperationDecl, PhaseDecl, Presentation, SortDecl, StateComparison,
    TranslatedStep, TranslatedWord, WordTranslation,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::Verdict;
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::solver::solve_diagram_task;
use archsig_common::canonical::Json;
use std::collections::BTreeMap;

pub(super) fn orig(id: &str) -> SourceRef {
    SourceRef::new(id, OriginKind::HumanAdopted).with_location(
        "diagram-test",
        "diag.law",
        Some((1, 20)),
    )
}

pub(super) fn clit(d: &CoeffDomain, n: i64) -> PolyExpr {
    match d {
        CoeffDomain::Z => PolyExpr::int(n),
        CoeffDomain::Q => PolyExpr::rat(n, 1).expect("rat"),
        CoeffDomain::Fp(m) => {
            PolyExpr::Const(ScalarLit::fp(num_bigint::BigInt::from(n), m.clone()).expect("fp"))
        }
    }
}

pub(super) fn ledger_base(name: &str, domain: CoeffDomain) -> Presentation {
    Presentation {
        name: name.into(),
        coeff_domain: domain.clone(),
        sorts: vec![SortDecl {
            name: "D".into(),
            rank: 1,
            coeff_domain: domain,
            provenance: Some(orig("sort-d")),
        }],
        phases: vec![PhaseDecl {
            name: "S".into(),
            coords: vec![CoordDecl::symbolic("x", "D")],
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "apply".into(),
            source_phase: "S".into(),
            target_phase: "S".into(),
            args: vec![("u".into(), "D".into())],
            domain_laws: vec![],
            updates: BTreeMap::from([("x".into(), PolyExpr::state("x") + PolyExpr::arg("u"))]),
            provenance: None,
        }],
        observations: vec![ObservationDecl {
            name: "read".into(),
            phase: "S".into(),
            components: vec![PolyExpr::state("x")],
            provenance: None,
        }],
        provenance: Provenance::new(vec![orig("base")], vec![MathClause::G140F1]),
    }
}

pub(super) fn weighted_branch(name: &str, domain: CoeffDomain, k: PolyExpr) -> Presentation {
    let one = clit(&domain, 1);
    Presentation {
        name: name.into(),
        coeff_domain: domain.clone(),
        sorts: vec![SortDecl {
            name: "D".into(),
            rank: 1,
            coeff_domain: domain,
            provenance: Some(orig("sort-d")),
        }],
        phases: vec![PhaseDecl {
            name: "S".into(),
            coords: vec![CoordDecl::symbolic("b", "D"), CoordDecl::symbolic("c", "D")],
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "apply".into(),
            source_phase: "S".into(),
            target_phase: "S".into(),
            args: vec![("u".into(), "D".into())],
            domain_laws: vec![],
            updates: BTreeMap::from([
                (
                    "b".into(),
                    PolyExpr::state("b") + k.clone() * PolyExpr::arg("u"),
                ),
                (
                    "c".into(),
                    PolyExpr::state("c") + (one - k) * PolyExpr::arg("u"),
                ),
            ]),
            provenance: None,
        }],
        observations: vec![ObservationDecl {
            name: "read".into(),
            phase: "S".into(),
            components: vec![PolyExpr::state("b") + PolyExpr::state("c")],
            provenance: None,
        }],
        provenance: Provenance::new(vec![orig(name)], vec![MathClause::G140F1]),
    }
}

pub(super) fn sum_to_x_morphism(src: &str, tgt: &str) -> StateMorphism {
    StateMorphism {
        source: src.into(),
        target: tgt.into(),
        state_comparisons: vec![StateComparison {
            after_phase: "S".into(),
            before_phase: "S".into(),
            map: BTreeMap::from([("x".into(), PolyExpr::state("b") + PolyExpr::state("c"))]),
            provenance: None,
        }],
        word_translation: WordTranslation {
            entries: vec![TranslatedWord {
                after_operation: "apply".into(),
                steps: vec![TranslatedStep {
                    before_operation: "apply".into(),
                    arg_exprs: vec![PolyExpr::arg("u")],
                }],
                provenance: None,
            }],
        },
        provenance: None,
    }
}

pub(super) fn id_bc_morphism(src: &str, tgt: &str) -> StateMorphism {
    StateMorphism {
        source: src.into(),
        target: tgt.into(),
        state_comparisons: vec![StateComparison {
            after_phase: "S".into(),
            before_phase: "S".into(),
            map: BTreeMap::from([
                ("b".into(), PolyExpr::state("b")),
                ("c".into(), PolyExpr::state("c")),
            ]),
            provenance: None,
        }],
        word_translation: WordTranslation {
            entries: vec![TranslatedWord {
                after_operation: "apply".into(),
                steps: vec![TranslatedStep {
                    before_operation: "apply".into(),
                    arg_exprs: vec![PolyExpr::arg("u")],
                }],
                provenance: None,
            }],
        },
        provenance: None,
    }
}

#[test]
fn diagram_square_completion_fork_both_directions() {
    for direction in [MorphismDirection::StateMap, MorphismDirection::TimeOrder] {
        let q = CoeffDomain::Q;
        let a = ledger_base("A", q.clone());
        let b = weighted_branch("B", q.clone(), clit(&q, 2));
        let c = weighted_branch("C", q.clone(), clit(&q, 2));
        let z = weighted_branch("Z", q.clone(), PolyExpr::param("kz"));
        let mut u_m = id_bc_morphism("Z", "B");
        u_m.state_comparisons[0]
            .map
            .insert("b".into(), PolyExpr::param("su") * PolyExpr::state("b"));

        let (edges, rel_lhs, rel_rhs) = match direction {
            MorphismDirection::StateMap => (
                vec![
                    DiagramEdge {
                        name: "f".into(),
                        source: "B".into(),
                        target: "A".into(),
                        morphism: sum_to_x_morphism("B", "A"),
                        is_fixed: true,
                        provenance: None,
                    },
                    DiagramEdge {
                        name: "g".into(),
                        source: "C".into(),
                        target: "A".into(),
                        morphism: sum_to_x_morphism("C", "A"),
                        is_fixed: true,
                        provenance: None,
                    },
                    DiagramEdge {
                        name: "u".into(),
                        source: "Z".into(),
                        target: "B".into(),
                        morphism: u_m,
                        is_fixed: false,
                        provenance: None,
                    },
                    DiagramEdge {
                        name: "v".into(),
                        source: "Z".into(),
                        target: "C".into(),
                        morphism: id_bc_morphism("Z", "C"),
                        is_fixed: false,
                        provenance: None,
                    },
                ],
                vec!["u".into(), "f".into()],
                vec!["v".into(), "g".into()],
            ),
            MorphismDirection::TimeOrder => (
                vec![
                    DiagramEdge {
                        name: "f".into(),
                        source: "A".into(),
                        target: "B".into(),
                        morphism: sum_to_x_morphism("B", "A"),
                        is_fixed: true,
                        provenance: None,
                    },
                    DiagramEdge {
                        name: "g".into(),
                        source: "A".into(),
                        target: "C".into(),
                        morphism: sum_to_x_morphism("C", "A"),
                        is_fixed: true,
                        provenance: None,
                    },
                    DiagramEdge {
                        name: "u".into(),
                        source: "B".into(),
                        target: "Z".into(),
                        morphism: u_m,
                        is_fixed: false,
                        provenance: None,
                    },
                    DiagramEdge {
                        name: "v".into(),
                        source: "C".into(),
                        target: "Z".into(),
                        morphism: id_bc_morphism("Z", "C"),
                        is_fixed: false,
                        provenance: None,
                    },
                ],
                vec!["f".into(), "u".into()],
                vec!["g".into(), "v".into()],
            ),
        };

        let spec = DiagramSpec {
            name: "pr_merge_square".into(),
            direction,
            vertices: vec![
                DiagramVertex {
                    name: "A".into(),
                    presentation: a,
                    is_fixed: true,
                    provenance: None,
                },
                DiagramVertex {
                    name: "B".into(),
                    presentation: b,
                    is_fixed: true,
                    provenance: None,
                },
                DiagramVertex {
                    name: "C".into(),
                    presentation: c,
                    is_fixed: true,
                    provenance: None,
                },
                DiagramVertex {
                    name: "Z".into(),
                    presentation: z,
                    is_fixed: false,
                    provenance: None,
                },
            ],
            edges,
            relations: vec![DiagramRelation {
                name: "square".into(),
                lhs: rel_lhs,
                rhs: rel_rhs,
                provenance: None,
            }],
            change_spec: ChangeSpec {
                name: "H".into(),
                coeff_domain: q.clone(),
                parameters: vec![
                    ParamDecl {
                        name: "su".into(),
                        coeff_domain: q.clone(),
                        provenance: None,
                    },
                    ParamDecl {
                        name: "kz".into(),
                        coeff_domain: q,
                        provenance: None,
                    },
                ],
                fixed: vec![
                    FixedTarget::OperationExpr {
                        presentation: "B".into(),
                        operation: "apply".into(),
                    },
                    FixedTarget::OperationExpr {
                        presentation: "C".into(),
                        operation: "apply".into(),
                    },
                ],
                editable: vec![EditableTarget::OperationExpr {
                    presentation: "Z".into(),
                    operation: "apply".into(),
                }],
                provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140F1]),
            },
            eval_condition: None,
            edge_eval_conditions: BTreeMap::new(),
            provenance: Provenance::new(vec![orig("diag")], vec![MathClause::G140F1]),
        };

        let checked = CheckedDiagramTask::validate(spec).expect("valid square task");
        let out = solve_diagram_task(&checked);
        assert_eq!(out.verdict, Verdict::Established, "direction={direction:?}");
        let detail = out.diagram.as_ref().expect("diagram detail");
        let restored = detail.restored_diagram.as_ref().expect("restored diagram");
        assert!(restored.reeval.matched);
        assert_eq!(
            restored.parameter_assignments.get("su").map(String::as_str),
            Some("1")
        );
        assert_eq!(
            restored.parameter_assignments.get("kz").map(String::as_str),
            Some("2")
        );
        assert!(detail.commutativity_residuals["square"].is_empty());
        assert!(matches!(out.to_json(), Json::Obj(_)));
    }
}

#[test]
fn diagram_chain_completion_restores_middle_vertex_and_morphisms() {
    let q = CoeffDomain::Q;
    let z = weighted_branch("Z", q.clone(), clit(&q, 1));
    let m = weighted_branch("M", q.clone(), PolyExpr::param("km"));
    let a = ledger_base("A", q.clone());
    let spec = DiagramSpec {
        name: "chain".into(),
        direction: MorphismDirection::StateMap,
        vertices: vec![
            DiagramVertex {
                name: "Z".into(),
                presentation: z,
                is_fixed: true,
                provenance: None,
            },
            DiagramVertex {
                name: "M".into(),
                presentation: m,
                is_fixed: false,
                provenance: None,
            },
            DiagramVertex {
                name: "A".into(),
                presentation: a,
                is_fixed: true,
                provenance: None,
            },
        ],
        edges: vec![
            DiagramEdge {
                name: "e1".into(),
                source: "Z".into(),
                target: "M".into(),
                morphism: StateMorphism {
                    source: "Z".into(),
                    target: "M".into(),
                    state_comparisons: vec![StateComparison {
                        after_phase: "S".into(),
                        before_phase: "S".into(),
                        map: BTreeMap::from([
                            (
                                "b".into(),
                                PolyExpr::param("sb") * PolyExpr::state("b") + PolyExpr::state("c"),
                            ),
                            ("c".into(), clit(&q, 0)),
                        ]),
                        provenance: None,
                    }],
                    word_translation: id_bc_morphism("Z", "M").word_translation,
                    provenance: None,
                },
                is_fixed: false,
                provenance: None,
            },
            DiagramEdge {
                name: "e2".into(),
                source: "M".into(),
                target: "A".into(),
                morphism: sum_to_x_morphism("M", "A"),
                is_fixed: false,
                provenance: None,
            },
        ],
        relations: vec![],
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: q.clone(),
            parameters: vec![
                ParamDecl {
                    name: "km".into(),
                    coeff_domain: q.clone(),
                    provenance: None,
                },
                ParamDecl {
                    name: "sb".into(),
                    coeff_domain: q,
                    provenance: None,
                },
            ],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140F1Dot1]),
        },
        eval_condition: None,
        edge_eval_conditions: BTreeMap::new(),
        provenance: Provenance::new(vec![orig("chain")], vec![MathClause::G140F1Dot1]),
    };

    let checked = CheckedDiagramTask::validate(spec).expect("valid chain");
    let out = solve_diagram_task(&checked);
    assert_eq!(out.verdict, Verdict::Established);
    let rd = out.diagram.unwrap().restored_diagram.unwrap();
    assert!(rd.reeval.matched);
    assert_eq!(rd.vertices.len(), 3);
    assert_eq!(rd.edges.len(), 2);
}

#[test]
fn diagram_incompatible_square_refuted_with_empty_witness() {
    let q = CoeffDomain::Q;
    let a = ledger_base("A", q.clone());
    let b = weighted_branch("B", q.clone(), clit(&q, 1));
    let c = weighted_branch("C", q.clone(), clit(&q, 0));
    let z = weighted_branch("Z", q.clone(), PolyExpr::param("kz"));
    let spec = DiagramSpec {
        name: "incompatible_square".into(),
        direction: MorphismDirection::StateMap,
        vertices: vec![
            DiagramVertex {
                name: "A".into(),
                presentation: a,
                is_fixed: true,
                provenance: None,
            },
            DiagramVertex {
                name: "B".into(),
                presentation: b,
                is_fixed: true,
                provenance: None,
            },
            DiagramVertex {
                name: "C".into(),
                presentation: c,
                is_fixed: true,
                provenance: None,
            },
            DiagramVertex {
                name: "Z".into(),
                presentation: z,
                is_fixed: false,
                provenance: None,
            },
        ],
        edges: vec![
            DiagramEdge {
                name: "f".into(),
                source: "B".into(),
                target: "A".into(),
                morphism: sum_to_x_morphism("B", "A"),
                is_fixed: true,
                provenance: None,
            },
            DiagramEdge {
                name: "g".into(),
                source: "C".into(),
                target: "A".into(),
                morphism: sum_to_x_morphism("C", "A"),
                is_fixed: true,
                provenance: None,
            },
            DiagramEdge {
                name: "u".into(),
                source: "Z".into(),
                target: "B".into(),
                morphism: id_bc_morphism("Z", "B"),
                is_fixed: false,
                provenance: None,
            },
            DiagramEdge {
                name: "v".into(),
                source: "Z".into(),
                target: "C".into(),
                morphism: id_bc_morphism("Z", "C"),
                is_fixed: false,
                provenance: None,
            },
        ],
        relations: vec![DiagramRelation {
            name: "sq".into(),
            lhs: vec!["u".into(), "f".into()],
            rhs: vec!["v".into(), "g".into()],
            provenance: None,
        }],
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: q.clone(),
            parameters: vec![ParamDecl {
                name: "kz".into(),
                coeff_domain: q,
                provenance: None,
            }],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140F1]),
        },
        eval_condition: None,
        edge_eval_conditions: BTreeMap::new(),
        provenance: Provenance::new(vec![orig("incompat")], vec![MathClause::G140F1]),
    };

    let checked = CheckedDiagramTask::validate(spec).expect("valid");
    let out = solve_diagram_task(&checked);
    assert_eq!(out.verdict, Verdict::Refuted);
    assert!(out.empty_witness.is_some());
}
