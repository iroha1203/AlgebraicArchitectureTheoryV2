use super::tests_diagram::{
    clit, id_bc_morphism, ledger_base, orig, sum_to_x_morphism, weighted_branch,
};
use crate::ir::change::{ChangeSpec, EvalCondition, NamedPoly, ParamDecl, PointDomain};
use crate::ir::diagram::{
    CheckedDiagramTask, DiagramEdge, DiagramRelation, DiagramSpec, DiagramVertex,
};
use crate::ir::morphism::{MorphismDirection, StateMorphism};
use crate::ir::presentation::{
    CoordDecl, LawKind, OperationDecl, StateComparison, StateLaw, TranslatedStep, TranslatedWord,
};
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::solver::solve_diagram_task;
use std::collections::BTreeMap;

#[test]
fn diagram_observation_match_cannot_fake_commutativity_and_structural_mismatch_rejected() {
    let q = CoeffDomain::Q;
    let a = weighted_branch("A", q.clone(), clit(&q, 1));
    let b = weighted_branch("B", q.clone(), clit(&q, 1));
    let mut z = weighted_branch("Z", q.clone(), clit(&q, 1));
    z.operations.push(OperationDecl {
        name: "noop".into(),
        source_phase: "S".into(),
        target_phase: "S".into(),
        args: vec![],
        domain_laws: vec![],
        updates: BTreeMap::from([
            ("b".into(), PolyExpr::state("b")),
            ("c".into(), PolyExpr::state("c")),
        ]),
        provenance: None,
    });

    let mut u_m = id_bc_morphism("Z", "B");
    u_m.word_translation.entries.push(TranslatedWord {
        after_operation: "noop".into(),
        steps: vec![TranslatedStep {
            before_operation: "apply".into(),
            arg_exprs: vec![clit(&q, 0)],
        }],
        provenance: None,
    });
    let mut v_m = StateMorphism {
        source: "Z".into(),
        target: "A".into(),
        state_comparisons: vec![StateComparison {
            after_phase: "S".into(),
            before_phase: "S".into(),
            map: BTreeMap::from([
                ("b".into(), PolyExpr::state("b") + clit(&q, 1)),
                ("c".into(), PolyExpr::state("c") - clit(&q, 1)),
            ]),
            provenance: None,
        }],
        word_translation: u_m.word_translation.clone(),
        provenance: None,
    };
    let spec_state_diff = DiagramSpec {
        name: "obs_fake_comm".into(),
        direction: MorphismDirection::StateMap,
        vertices: vec![
            DiagramVertex {
                name: "Z".into(),
                presentation: z.clone(),
                is_fixed: true,
                provenance: None,
            },
            DiagramVertex {
                name: "B".into(),
                presentation: b.clone(),
                is_fixed: true,
                provenance: None,
            },
            DiagramVertex {
                name: "A".into(),
                presentation: a.clone(),
                is_fixed: true,
                provenance: None,
            },
        ],
        edges: vec![
            DiagramEdge {
                name: "u".into(),
                source: "Z".into(),
                target: "B".into(),
                morphism: u_m.clone(),
                is_fixed: true,
                provenance: None,
            },
            DiagramEdge {
                name: "f".into(),
                source: "B".into(),
                target: "A".into(),
                morphism: id_bc_morphism("B", "A"),
                is_fixed: true,
                provenance: None,
            },
            DiagramEdge {
                name: "v".into(),
                source: "Z".into(),
                target: "A".into(),
                morphism: v_m.clone(),
                is_fixed: true,
                provenance: None,
            },
        ],
        relations: vec![DiagramRelation {
            name: "comm".into(),
            lhs: vec!["u".into(), "f".into()],
            rhs: vec!["v".into()],
            provenance: None,
        }],
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: q.clone(),
            parameters: vec![],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140F1]),
        },
        eval_condition: None,
        edge_eval_conditions: BTreeMap::new(),
        provenance: Provenance::new(vec![orig("obs")], vec![MathClause::G140F1]),
    };
    assert_eq!(
        solve_diagram_task(&CheckedDiagramTask::validate(spec_state_diff).unwrap()).verdict,
        Verdict::Refuted
    );

    v_m.state_comparisons[0].map = BTreeMap::from([
        ("b".into(), PolyExpr::state("b")),
        ("c".into(), PolyExpr::state("c")),
    ]);
    v_m.word_translation.entries[1].steps.clear();
    let spec_wt_diff = DiagramSpec {
        name: "wt_mismatch".into(),
        direction: MorphismDirection::StateMap,
        vertices: vec![
            DiagramVertex {
                name: "Z".into(),
                presentation: z,
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
                name: "A".into(),
                presentation: a,
                is_fixed: true,
                provenance: None,
            },
        ],
        edges: vec![
            DiagramEdge {
                name: "u".into(),
                source: "Z".into(),
                target: "B".into(),
                morphism: u_m,
                is_fixed: true,
                provenance: None,
            },
            DiagramEdge {
                name: "f".into(),
                source: "B".into(),
                target: "A".into(),
                morphism: id_bc_morphism("B", "A"),
                is_fixed: true,
                provenance: None,
            },
            DiagramEdge {
                name: "v".into(),
                source: "Z".into(),
                target: "A".into(),
                morphism: v_m,
                is_fixed: true,
                provenance: None,
            },
        ],
        relations: vec![DiagramRelation {
            name: "comm".into(),
            lhs: vec!["u".into(), "f".into()],
            rhs: vec!["v".into()],
            provenance: None,
        }],
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: q,
            parameters: vec![],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140F1]),
        },
        eval_condition: None,
        edge_eval_conditions: BTreeMap::new(),
        provenance: Provenance::new(vec![orig("wt")], vec![MathClause::G140F1]),
    };
    let out_wt = solve_diagram_task(&CheckedDiagramTask::validate(spec_wt_diff).unwrap());
    assert_eq!(out_wt.verdict, Verdict::Refuted);
    assert!(
        out_wt
            .diagram
            .unwrap()
            .structural_mismatches
            .contains_key("comm")
    );
}

#[test]
fn diagram_quotient_ideal_and_silence_disciplines() {
    let q = CoeffDomain::Q;
    let mut z = weighted_branch("Z", q.clone(), clit(&q, 1));
    z.phases[0].state_laws.push(StateLaw {
        name: "c_zero".into(),
        kind: LawKind::Representation,
        polynomial: PolyExpr::state("c"),
        provenance: None,
    });
    z.operations[0]
        .updates
        .insert("c".into(), PolyExpr::state("c"));
    let a = ledger_base("A", q.clone());
    let m_mod = StateMorphism {
        source: "Z".into(),
        target: "A".into(),
        state_comparisons: vec![StateComparison {
            after_phase: "S".into(),
            before_phase: "S".into(),
            map: BTreeMap::from([("x".into(), PolyExpr::state("b"))]),
            provenance: None,
        }],
        word_translation: sum_to_x_morphism("Z", "A").word_translation,
        provenance: None,
    };
    let q_spec = DiagramSpec {
        name: "quotient_diag".into(),
        direction: MorphismDirection::StateMap,
        vertices: vec![
            DiagramVertex {
                name: "Z".into(),
                presentation: z,
                is_fixed: true,
                provenance: None,
            },
            DiagramVertex {
                name: "A".into(),
                presentation: a,
                is_fixed: true,
                provenance: None,
            },
        ],
        edges: vec![DiagramEdge {
            name: "e".into(),
            source: "Z".into(),
            target: "A".into(),
            morphism: m_mod,
            is_fixed: true,
            provenance: None,
        }],
        relations: vec![],
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: q.clone(),
            parameters: vec![],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G141D5]),
        },
        eval_condition: None,
        edge_eval_conditions: BTreeMap::new(),
        provenance: Provenance::new(vec![orig("q")], vec![MathClause::G141D5]),
    };
    assert_eq!(
        solve_diagram_task(&CheckedDiagramTask::validate(q_spec).unwrap()).verdict,
        Verdict::Established
    );

    let mut z_unobs = weighted_branch("Z", q.clone(), clit(&q, 1));
    z_unobs.phases[0]
        .coords
        .push(CoordDecl::missing("unobs_c", "D"));
    z_unobs.operations[0]
        .updates
        .insert("unobs_c".into(), PolyExpr::unobserved("Z.S.unobs_c", None));
    let u_spec = DiagramSpec {
        name: "unobs_diag".into(),
        direction: MorphismDirection::StateMap,
        vertices: vec![DiagramVertex {
            name: "Z".into(),
            presentation: z_unobs,
            is_fixed: false,
            provenance: None,
        }],
        edges: vec![],
        relations: vec![],
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: q.clone(),
            parameters: vec![],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140F1]),
        },
        eval_condition: None,
        edge_eval_conditions: BTreeMap::new(),
        provenance: Provenance::new(vec![orig("u")], vec![MathClause::G140F1]),
    };
    assert!(matches!(
        solve_diagram_task(&CheckedDiagramTask::validate(u_spec).unwrap()).verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { .. })
    ));

    let nl_spec = DiagramSpec {
        name: "nl_rat".into(),
        direction: MorphismDirection::StateMap,
        vertices: vec![
            DiagramVertex {
                name: "Z".into(),
                presentation: weighted_branch("Z", q.clone(), clit(&q, 1)),
                is_fixed: false,
                provenance: None,
            },
            DiagramVertex {
                name: "A".into(),
                presentation: ledger_base("A", q.clone()),
                is_fixed: true,
                provenance: None,
            },
        ],
        edges: vec![DiagramEdge {
            name: "e".into(),
            source: "Z".into(),
            target: "A".into(),
            morphism: sum_to_x_morphism("Z", "A"),
            is_fixed: false,
            provenance: None,
        }],
        relations: vec![],
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: q.clone(),
            parameters: vec![ParamDecl {
                name: "k".into(),
                coeff_domain: q.clone(),
                provenance: None,
            }],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G141D4]),
        },
        eval_condition: Some(EvalCondition {
            name: "nl".into(),
            evaluations: vec![],
            equations: vec![NamedPoly {
                name: "circle".into(),
                expr: PolyExpr::pow(PolyExpr::param("k"), 2) - clit(&q, 2),
                provenance: None,
            }],
            invertibles: vec![],
            point_domain: PointDomain::RationalPoints,
            provenance: Provenance::new(vec![orig("ev")], vec![MathClause::G141D4]),
        }),
        edge_eval_conditions: BTreeMap::new(),
        provenance: Provenance::new(vec![orig("nl")], vec![MathClause::G141D4]),
    };
    assert!(matches!(
        solve_diagram_task(&CheckedDiagramTask::validate(nl_spec).unwrap()).verdict,
        Verdict::Undetermined(SilenceReason::NonLinearRationalOrIntegerExistence { .. })
    ));

    let fp = CoeffDomain::Fp(num_bigint::BigUint::from(5u32));
    let fp_spec = DiagramSpec {
        name: "fp_diag".into(),
        direction: MorphismDirection::StateMap,
        vertices: vec![
            DiagramVertex {
                name: "B".into(),
                presentation: weighted_branch("B", fp.clone(), PolyExpr::param("k")),
                is_fixed: false,
                provenance: None,
            },
            DiagramVertex {
                name: "A".into(),
                presentation: ledger_base("A", fp.clone()),
                is_fixed: true,
                provenance: None,
            },
        ],
        edges: vec![DiagramEdge {
            name: "e".into(),
            source: "B".into(),
            target: "A".into(),
            morphism: sum_to_x_morphism("B", "A"),
            is_fixed: false,
            provenance: None,
        }],
        relations: vec![],
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: fp.clone(),
            parameters: vec![ParamDecl {
                name: "k".into(),
                coeff_domain: fp.clone(),
                provenance: None,
            }],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G141D4]),
        },
        eval_condition: Some(EvalCondition {
            name: "eq".into(),
            evaluations: vec![],
            equations: vec![NamedPoly {
                name: "pick".into(),
                expr: PolyExpr::param("k") - clit(&fp, 3),
                provenance: None,
            }],
            invertibles: vec![],
            point_domain: PointDomain::FiniteFieldPoints(num_bigint::BigUint::from(5u32)),
            provenance: Provenance::new(vec![orig("ev")], vec![MathClause::G141D4]),
        }),
        edge_eval_conditions: BTreeMap::new(),
        provenance: Provenance::new(vec![orig("fp")], vec![MathClause::G141D4]),
    };
    let out_fp = solve_diagram_task(&CheckedDiagramTask::validate(fp_spec).unwrap());
    assert_eq!(out_fp.verdict, Verdict::Established);
    assert_eq!(
        out_fp
            .diagram
            .unwrap()
            .restored_diagram
            .unwrap()
            .parameter_assignments
            .get("k")
            .map(String::as_str),
        Some("3")
    );

    let z_univ = DiagramSpec {
        name: "z_univ".into(),
        direction: MorphismDirection::StateMap,
        vertices: vec![
            DiagramVertex {
                name: "B".into(),
                presentation: weighted_branch("B", CoeffDomain::Z, PolyExpr::param("k")),
                is_fixed: false,
                provenance: None,
            },
            DiagramVertex {
                name: "A".into(),
                presentation: ledger_base("A", CoeffDomain::Z),
                is_fixed: true,
                provenance: None,
            },
        ],
        edges: vec![DiagramEdge {
            name: "e".into(),
            source: "B".into(),
            target: "A".into(),
            morphism: sum_to_x_morphism("B", "A"),
            is_fixed: false,
            provenance: None,
        }],
        relations: vec![],
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: CoeffDomain::Z,
            parameters: vec![ParamDecl {
                name: "k".into(),
                coeff_domain: CoeffDomain::Z,
                provenance: None,
            }],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G141D1]),
        },
        eval_condition: Some(EvalCondition {
            name: "univ".into(),
            evaluations: vec![],
            equations: vec![],
            invertibles: vec![],
            point_domain: PointDomain::UniversalRing,
            provenance: Provenance::new(vec![orig("ev")], vec![MathClause::G141D1]),
        }),
        edge_eval_conditions: BTreeMap::new(),
        provenance: Provenance::new(vec![orig("zu")], vec![MathClause::G141D1]),
    };
    assert!(matches!(
        solve_diagram_task(&CheckedDiagramTask::validate(z_univ).unwrap()).verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { ref condition, .. }) if condition == "universal_ring_solution_space_out_of_scope"
    ));
}

#[test]
fn diagram_review_regressions_m03_m01_m02() {
    use crate::algebra::VarOrder;
    use crate::solver::common_solve::try_decide_unit_z_quotients;
    use crate::solver::preservation::PreservationObligation;

    let q = CoeffDomain::Q;
    let eval_contradiction_spec = DiagramSpec {
        name: "m03_eval_eq_contradiction".into(),
        direction: MorphismDirection::StateMap,
        vertices: vec![
            DiagramVertex {
                name: "B".into(),
                presentation: weighted_branch("B", q.clone(), PolyExpr::param("k")),
                is_fixed: false,
                provenance: None,
            },
            DiagramVertex {
                name: "A".into(),
                presentation: ledger_base("A", q.clone()),
                is_fixed: true,
                provenance: None,
            },
        ],
        edges: vec![DiagramEdge {
            name: "e".into(),
            source: "B".into(),
            target: "A".into(),
            morphism: sum_to_x_morphism("B", "A"),
            is_fixed: false,
            provenance: None,
        }],
        relations: vec![],
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: q.clone(),
            parameters: vec![ParamDecl {
                name: "k".into(),
                coeff_domain: q.clone(),
                provenance: None,
            }],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G141D5]),
        },
        eval_condition: Some(EvalCondition {
            name: "ev1".into(),
            evaluations: vec![],
            equations: vec![NamedPoly {
                name: "k1".into(),
                expr: PolyExpr::param("k") - clit(&q, 1),
                provenance: None,
            }],
            invertibles: vec![],
            point_domain: PointDomain::AlgebraicClosure,
            provenance: Provenance::new(vec![orig("ev1")], vec![MathClause::G141D5]),
        }),
        edge_eval_conditions: BTreeMap::from([(
            "e".into(),
            EvalCondition {
                name: "ev2".into(),
                evaluations: vec![],
                equations: vec![NamedPoly {
                    name: "k2".into(),
                    expr: PolyExpr::param("k") - clit(&q, 2),
                    provenance: None,
                }],
                invertibles: vec![],
                point_domain: PointDomain::AlgebraicClosure,
                provenance: Provenance::new(vec![orig("ev2")], vec![MathClause::G141D5]),
            },
        )]),
        provenance: Provenance::new(vec![orig("m03a")], vec![MathClause::G141D5]),
    };
    let out_m03a =
        solve_diagram_task(&CheckedDiagramTask::validate(eval_contradiction_spec).unwrap());
    assert_eq!(out_m03a.verdict, Verdict::Refuted);
    assert!(out_m03a.empty_witness.is_some());
    assert!(!out_m03a.residual_ideal.is_empty());

    let inv_contradiction_spec = DiagramSpec {
        name: "m03_inv_contradiction".into(),
        direction: MorphismDirection::StateMap,
        vertices: vec![
            DiagramVertex {
                name: "B".into(),
                presentation: weighted_branch("B", q.clone(), PolyExpr::param("k")),
                is_fixed: false,
                provenance: None,
            },
            DiagramVertex {
                name: "A".into(),
                presentation: weighted_branch("A", q.clone(), clit(&q, 1)),
                is_fixed: true,
                provenance: None,
            },
        ],
        edges: vec![DiagramEdge {
            name: "e".into(),
            source: "B".into(),
            target: "A".into(),
            morphism: id_bc_morphism("B", "A"),
            is_fixed: false,
            provenance: None,
        }],
        relations: vec![],
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: q.clone(),
            parameters: vec![ParamDecl {
                name: "k".into(),
                coeff_domain: q.clone(),
                provenance: None,
            }],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G141D5]),
        },
        eval_condition: Some(EvalCondition {
            name: "ev_inv".into(),
            evaluations: vec![],
            equations: vec![],
            invertibles: vec![NamedPoly {
                name: "k_minus_1_nz".into(),
                expr: PolyExpr::param("k") - clit(&q, 1),
                provenance: None,
            }],
            point_domain: PointDomain::AlgebraicClosure,
            provenance: Provenance::new(vec![orig("ev_inv")], vec![MathClause::G141D5]),
        }),
        edge_eval_conditions: BTreeMap::new(),
        provenance: Provenance::new(vec![orig("m03b")], vec![MathClause::G141D5]),
    };
    let out_m03b =
        solve_diagram_task(&CheckedDiagramTask::validate(inv_contradiction_spec).unwrap());
    assert_eq!(out_m03b.verdict, Verdict::Refuted);
    assert!(out_m03b.empty_witness.is_some());
    assert!(!out_m03b.residual_ideal.is_empty());

    let nl_inv_spec = DiagramSpec {
        name: "m01_affine_eq_nonlinear_inv".into(),
        direction: MorphismDirection::StateMap,
        vertices: vec![
            DiagramVertex {
                name: "B".into(),
                presentation: weighted_branch("B", q.clone(), PolyExpr::param("k")),
                is_fixed: false,
                provenance: None,
            },
            DiagramVertex {
                name: "A".into(),
                presentation: ledger_base("A", q.clone()),
                is_fixed: true,
                provenance: None,
            },
        ],
        edges: vec![DiagramEdge {
            name: "e".into(),
            source: "B".into(),
            target: "A".into(),
            morphism: sum_to_x_morphism("B", "A"),
            is_fixed: false,
            provenance: None,
        }],
        relations: vec![],
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: q.clone(),
            parameters: vec![ParamDecl {
                name: "k".into(),
                coeff_domain: q.clone(),
                provenance: None,
            }],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G141D4]),
        },
        eval_condition: Some(EvalCondition {
            name: "rat_nl_inv".into(),
            evaluations: vec![],
            equations: vec![NamedPoly {
                name: "pick2".into(),
                expr: PolyExpr::param("k") - clit(&q, 2),
                provenance: None,
            }],
            invertibles: vec![NamedPoly {
                name: "k2_minus_1".into(),
                expr: PolyExpr::pow(PolyExpr::param("k"), 2) - clit(&q, 1),
                provenance: None,
            }],
            point_domain: PointDomain::RationalPoints,
            provenance: Provenance::new(vec![orig("rat_nl_inv")], vec![MathClause::G141D4]),
        }),
        edge_eval_conditions: BTreeMap::new(),
        provenance: Provenance::new(vec![orig("m01")], vec![MathClause::G141D4]),
    };
    let out_nl_inv = solve_diagram_task(&CheckedDiagramTask::validate(nl_inv_spec).unwrap());
    assert_eq!(out_nl_inv.verdict, Verdict::Established);
    assert_eq!(
        out_nl_inv
            .diagram
            .unwrap()
            .restored_diagram
            .unwrap()
            .parameter_assignments
            .get("k")
            .map(String::as_str),
        Some("2")
    );

    let empty_order = VarOrder::new(vec![]).unwrap();
    let bad_q_extra = PolyExpr::rat(1, 2).unwrap();
    let ob = PreservationObligation {
        state_vars: vec!["x".into()],
        arg_vars: vec![],
        source_laws: vec![PolyExpr::state("x")],
        target: PolyExpr::state("x"),
    };
    let mut checks = Vec::new();
    let err = try_decide_unit_z_quotients(&[ob], &[bad_q_extra], &[], &empty_order, &mut checks);
    assert!(matches!(
        err,
        Err(SilenceReason::ApplicabilityConditionNotMet { .. })
    ));
}
