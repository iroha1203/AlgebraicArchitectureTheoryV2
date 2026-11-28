use super::*;
use archsig_common::canonical::Json;
use std::collections::BTreeMap;

fn origin() -> SourceRef {
    SourceRef::new("phase2-ir-test", OriginKind::HumanAdopted).with_location(
        "unit-test",
        "phase2.law",
        Some((1, 20)),
    )
}

fn eval_expr_rat(expr: &PolyExpr, states: &[(&str, i64)], args: &[(&str, i64)]) -> i64 {
    match expr {
        PolyExpr::Const(ScalarLit::Q { num, den }) => {
            assert_eq!(*den, num_bigint::BigInt::from(1));
            num.try_into().expect("fits i64")
        }
        PolyExpr::Const(ScalarLit::Z(n)) => n.try_into().expect("fits i64"),
        PolyExpr::StateVar(v) => states
            .iter()
            .find(|(k, _)| k == v)
            .map(|(_, val)| *val)
            .expect("state var bound"),
        PolyExpr::ArgVar(v) => args
            .iter()
            .find(|(k, _)| k == v)
            .map(|(_, val)| *val)
            .expect("arg var bound"),
        PolyExpr::Neg(a) => -eval_expr_rat(a, states, args),
        PolyExpr::Add(a, b) => eval_expr_rat(a, states, args) + eval_expr_rat(b, states, args),
        PolyExpr::Sub(a, b) => eval_expr_rat(a, states, args) - eval_expr_rat(b, states, args),
        PolyExpr::Mul(a, b) => eval_expr_rat(a, states, args) * eval_expr_rat(b, states, args),
        PolyExpr::Pow(a, e) => eval_expr_rat(a, states, args).pow(*e),
        other => panic!("unexpected expr node in eval helper: {other:?}"),
    }
}

fn mk_op(
    name: &str,
    src: &str,
    tgt: &str,
    arg: &str,
    updates: Vec<(&str, PolyExpr)>,
) -> OperationDecl {
    OperationDecl {
        name: name.into(),
        source_phase: src.into(),
        target_phase: tgt.into(),
        args: vec![(arg.into(), "D".into())],
        domain_laws: vec![],
        updates: updates.into_iter().map(|(k, v)| (k.into(), v)).collect(),
        provenance: None,
    }
}

fn mk_pres_z(name: &str, phases: Vec<PhaseDecl>, ops: Vec<OperationDecl>) -> Presentation {
    Presentation {
        name: name.into(),
        coeff_domain: CoeffDomain::Z,
        sorts: vec![SortDecl {
            name: "D".into(),
            rank: 1,
            coeff_domain: CoeffDomain::Z,
            provenance: None,
        }],
        phases,
        operations: ops,
        observations: vec![],
        provenance: Provenance::new(vec![origin()], vec![MathClause::G140F2]),
    }
}

fn mk_phase(name: &str, coords: &[&str], laws: Vec<StateLaw>) -> PhaseDecl {
    PhaseDecl {
        name: name.into(),
        coords: coords
            .iter()
            .map(|c| CoordDecl::symbolic(*c, "D"))
            .collect(),
        state_laws: laws,
        provenance: None,
    }
}

fn single_phase_pres(name: &str, domain: CoeffDomain, coeff_scale: i64) -> Presentation {
    let orig = origin();
    Presentation {
        name: name.into(),
        coeff_domain: domain.clone(),
        sorts: vec![SortDecl {
            name: "D".into(),
            rank: 1,
            coeff_domain: domain,
            provenance: Some(orig.clone()),
        }],
        phases: vec![PhaseDecl {
            name: "Active".into(),
            coords: vec![CoordDecl::symbolic("x", "D")],
            state_laws: vec![StateLaw {
                name: "sem_ok".into(),
                kind: LawKind::Semantic,
                polynomial: PolyExpr::int(0),
                provenance: Some(orig.clone()),
            }],
            provenance: Some(orig.clone()),
        }],
        operations: vec![OperationDecl {
            name: "apply".into(),
            source_phase: "Active".into(),
            target_phase: "Active".into(),
            args: vec![("u".into(), "D".into())],
            domain_laws: vec![],
            updates: BTreeMap::from([(
                "x".into(),
                PolyExpr::state("x") + PolyExpr::int(coeff_scale) * PolyExpr::arg("u"),
            )]),
            provenance: Some(orig.clone()),
        }],
        observations: vec![ObservationDecl {
            name: "read".into(),
            phase: "Active".into(),
            components: vec![PolyExpr::state("x")],
            provenance: Some(orig.clone()),
        }],
        provenance: Provenance::new(vec![orig], vec![MathClause::G140F1]),
    }
}

fn apply_cmp_morphism(src: &str, tgt: &str, x_expr: PolyExpr) -> StateMorphism {
    StateMorphism {
        source: src.into(),
        target: tgt.into(),
        state_comparisons: vec![StateComparison {
            after_phase: "Active".into(),
            before_phase: "Active".into(),
            map: BTreeMap::from([("x".into(), x_expr)]),
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

fn multi_step_chain_fixture() -> (
    Presentation,
    Presentation,
    Presentation,
    Presentation,
    StateMorphism,
    StateMorphism,
    StateMorphism,
) {
    let p3 = mk_pres_z(
        "P3",
        vec![
            mk_phase("Idle", &["x"], vec![]),
            mk_phase(
                "Busy",
                &["x", "c"],
                vec![StateLaw {
                    name: "repr_c".into(),
                    kind: LawKind::Representation,
                    polynomial: PolyExpr::state("c") - PolyExpr::state("x"),
                    provenance: None,
                }],
            ),
        ],
        vec![mk_op(
            "bump",
            "Busy",
            "Busy",
            "u",
            vec![
                ("x", PolyExpr::state("x") + PolyExpr::arg("u")),
                ("c", PolyExpr::state("c") + PolyExpr::arg("u")),
            ],
        )],
    );
    let p2 = mk_pres_z(
        "P2",
        vec![mk_phase("M", &["mx", "mc"], vec![])],
        vec![
            mk_op(
                "step1",
                "M",
                "M",
                "a",
                vec![
                    ("mx", PolyExpr::state("mx") + PolyExpr::arg("a")),
                    (
                        "mc",
                        PolyExpr::state("mc") + PolyExpr::int(2) * PolyExpr::arg("a"),
                    ),
                ],
            ),
            mk_op(
                "step2",
                "M",
                "M",
                "b",
                vec![
                    ("mx", PolyExpr::state("mx") + PolyExpr::arg("b")),
                    ("mc", PolyExpr::state("mc") + PolyExpr::arg("b")),
                ],
            ),
        ],
    );
    let p1 = mk_pres_z(
        "P1",
        vec![mk_phase("B", &["bx"], vec![])],
        vec![mk_op(
            "b_op",
            "B",
            "B",
            "v",
            vec![("bx", PolyExpr::state("bx") + PolyExpr::arg("v"))],
        )],
    );
    let p0 = mk_pres_z(
        "P0",
        vec![mk_phase("Z", &["zx"], vec![])],
        vec![mk_op(
            "z_op",
            "Z",
            "Z",
            "w",
            vec![("zx", PolyExpr::state("zx") + PolyExpr::arg("w"))],
        )],
    );

    let h1 = StateMorphism {
        source: "P3".into(),
        target: "P2".into(),
        state_comparisons: vec![
            StateComparison {
                after_phase: "Idle".into(),
                before_phase: "M".into(),
                map: BTreeMap::from([
                    ("mx".into(), PolyExpr::state("x")),
                    ("mc".into(), PolyExpr::int(0)),
                ]),
                provenance: None,
            },
            StateComparison {
                after_phase: "Busy".into(),
                before_phase: "M".into(),
                map: BTreeMap::from([
                    ("mx".into(), PolyExpr::state("x") + PolyExpr::int(1)),
                    ("mc".into(), PolyExpr::state("c")),
                ]),
                provenance: None,
            },
        ],
        word_translation: WordTranslation {
            entries: vec![TranslatedWord {
                after_operation: "bump".into(),
                steps: vec![
                    TranslatedStep {
                        before_operation: "step1".into(),
                        arg_exprs: vec![PolyExpr::state("x")],
                    },
                    TranslatedStep {
                        before_operation: "step2".into(),
                        arg_exprs: vec![PolyExpr::state("c") + PolyExpr::arg("u")],
                    },
                ],
                provenance: None,
            }],
        },
        provenance: None,
    };

    let h2 = StateMorphism {
        source: "P2".into(),
        target: "P1".into(),
        state_comparisons: vec![StateComparison {
            after_phase: "M".into(),
            before_phase: "B".into(),
            map: BTreeMap::from([("bx".into(), PolyExpr::state("mx") + PolyExpr::state("mc"))]),
            provenance: None,
        }],
        word_translation: WordTranslation {
            entries: vec![
                TranslatedWord {
                    after_operation: "step1".into(),
                    steps: vec![
                        TranslatedStep {
                            before_operation: "b_op".into(),
                            arg_exprs: vec![PolyExpr::state("mx")],
                        },
                        TranslatedStep {
                            before_operation: "b_op".into(),
                            arg_exprs: vec![
                                PolyExpr::int(3) * PolyExpr::arg("a") - PolyExpr::state("mx"),
                            ],
                        },
                    ],
                    provenance: None,
                },
                TranslatedWord {
                    after_operation: "step2".into(),
                    steps: vec![TranslatedStep {
                        before_operation: "b_op".into(),
                        arg_exprs: vec![PolyExpr::int(2) * PolyExpr::arg("b")],
                    }],
                    provenance: None,
                },
            ],
        },
        provenance: None,
    };

    let h3 = StateMorphism {
        source: "P1".into(),
        target: "P0".into(),
        state_comparisons: vec![StateComparison {
            after_phase: "B".into(),
            before_phase: "Z".into(),
            map: BTreeMap::from([("zx".into(), PolyExpr::int(3) * PolyExpr::state("bx"))]),
            provenance: None,
        }],
        word_translation: WordTranslation {
            entries: vec![TranslatedWord {
                after_operation: "b_op".into(),
                steps: vec![TranslatedStep {
                    before_operation: "z_op".into(),
                    arg_exprs: vec![PolyExpr::int(2) * PolyExpr::state("bx") + PolyExpr::arg("v")],
                }],
                provenance: None,
            }],
        },
        provenance: None,
    };

    (p3, p2, p1, p0, h1, h2, h3)
}

#[test]
fn identity_and_multistep_state_morphism_composition() {
    let (p3, p2, p1, p0, h1, h2, h3) = multi_step_chain_fixture();
    let id3 = identity_state_morphism(&p3);
    let id2 = identity_state_morphism(&p2);

    // 左・右単位元（多相・多ステップを含む）
    let right_id = compose_state_order(&h1, &id3, &p3, &p3).expect("h1 ∘ id_P3");
    let left_id = compose_state_order(&id2, &h1, &p3, &p2).expect("id_P2 ∘ h1");

    for lhs in [&right_id, &left_id] {
        assert_eq!(lhs.source, h1.source);
        assert_eq!(lhs.target, h1.target);
        let sc_l = &lhs.state_comparisons[1];
        let sc_r = &h1.state_comparisons[1];
        assert_eq!(
            eval_expr_rat(&sc_l.map["mx"], &[("x", 5), ("c", 7)], &[]),
            eval_expr_rat(&sc_r.map["mx"], &[("x", 5), ("c", 7)], &[])
        );
        let tw_l = lhs.word_translation.for_operation("bump").unwrap();
        let tw_r = h1.word_translation.for_operation("bump").unwrap();
        assert_eq!(tw_l.steps.len(), tw_r.steps.len());
        for (sl, sr) in tw_l.steps.iter().zip(&tw_r.steps) {
            assert_eq!(sl.before_operation, sr.before_operation);
            assert_eq!(
                eval_expr_rat(&sl.arg_exprs[0], &[("x", 5), ("c", 7)], &[("u", 3)]),
                eval_expr_rat(&sr.arg_exprs[0], &[("x", 5), ("c", 7)], &[("u", 3)])
            );
        }
    }

    // 中間状態更新を伴う 2 段翻訳の検証:
    // Busy (x=5, c=7), u=3 -> P2 開始: mx=6, mc=7
    // step1(a=5) -> [b_op(6), b_op(9)], P2 更新: (mx'=11, mc'=17)
    // step2(b=7+3=10) -> [b_op(20)]
    let h21 = compose_state_order(&h2, &h1, &p3, &p2).expect("h2 ∘ h1");
    let bump_21 = h21.word_translation.for_operation("bump").unwrap();
    let expected_21: Vec<i64> = vec![6, 9, 20];
    let actual_21: Vec<i64> = bump_21
        .steps
        .iter()
        .map(|st| eval_expr_rat(&st.arg_exprs[0], &[("x", 5), ("c", 7)], &[("u", 3)]))
        .collect();
    assert_eq!(actual_21, expected_21);

    // 結合則: h3 ∘ (h2 ∘ h1) == (h3 ∘ h2) ∘ h1
    let h32 = compose_state_order(&h3, &h2, &p2, &p1).expect("h3 ∘ h2");
    let lhs_assoc = compose_state_order(&h3, &h21, &p3, &p1).expect("h3 ∘ (h2 ∘ h1)");
    let rhs_assoc = compose_state_order(&h32, &h1, &p3, &p2).expect("(h3 ∘ h2) ∘ h1");

    assert_eq!(lhs_assoc.source, p3.name);
    assert_eq!(rhs_assoc.target, p0.name);
    let s = [("x", 5), ("c", 7)];
    let u = [("u", 3)];
    assert_eq!(
        eval_expr_rat(&lhs_assoc.state_comparisons[1].map["zx"], &s, &[]),
        eval_expr_rat(&rhs_assoc.state_comparisons[1].map["zx"], &s, &[])
    );
    let tw_l = lhs_assoc.word_translation.for_operation("bump").unwrap();
    let tw_r = rhs_assoc.word_translation.for_operation("bump").unwrap();
    assert_eq!(tw_l.steps.len(), 3);
    assert_eq!(tw_l.steps.len(), tw_r.steps.len());
    for ((a, b), expected) in tw_l.steps.iter().zip(&tw_r.steps).zip([32, 47, 76]) {
        assert_eq!(a.before_operation, b.before_operation);
        let lhs_val = eval_expr_rat(&a.arg_exprs[0], &s, &u);
        let rhs_val = eval_expr_rat(&b.arg_exprs[0], &s, &u);
        assert_eq!(lhs_val, expected);
        assert_eq!(rhs_val, expected);
    }

    // 始点不一致のエラー検査
    assert!(matches!(
        compose_state_order(&h2, &h3, &p1, &p2),
        Err(ValidationError::ConversionError { .. })
    ));
}

#[test]
fn time_step_morphism_orientation_and_contravariant_composition() {
    let (p3, p2, p1, _p0, h1, h2, _) = multi_step_chain_fixture();
    let bad = TimeStepMorphism::new("P2", "P1", h2.clone());
    assert!(matches!(bad, Err(ValidationError::ConversionError { .. })));

    let first = TimeStepMorphism::new("P1", "P2", h2).expect("valid P1 -> P2");
    let second = TimeStepMorphism::new("P2", "P3", h1).expect("valid P2 -> P3");
    let composed = compose_time_order(&first, &second, &p2, &p3).expect("compose time order");
    assert_eq!(composed.before(), "P1");
    assert_eq!(composed.after(), "P3");
    assert_eq!(composed.state_map().source, "P3");
    assert_eq!(composed.state_map().target, "P1");
    assert_eq!(
        eval_expr_rat(
            &composed.state_map().state_comparisons[0].map["bx"],
            &[("x", 9)],
            &[]
        ),
        9
    );

    let disjoint = compose_time_order(&second, &first, &p1, &p2);
    assert!(matches!(
        disjoint,
        Err(ValidationError::ConversionError { .. })
    ));
}

#[test]
fn checked_diagram_task_validation_positive_and_negative() {
    let orig = origin();
    let d = CoeffDomain::Z;
    let p0 = single_phase_pres("M0", d.clone(), 1);
    let mut p1 = single_phase_pres("M1", d.clone(), 1);
    p1.phases[0].state_laws.push(StateLaw {
        name: "repr_extra".into(),
        kind: LawKind::Representation,
        polynomial: PolyExpr::param("a") * PolyExpr::state("x"),
        provenance: None,
    });
    let mut p2 = single_phase_pres("M2", d.clone(), 1);
    p2.operations[0].updates.insert(
        "x".into(),
        PolyExpr::state("x") + PolyExpr::param("b") * PolyExpr::arg("u"),
    );

    let base_change = ChangeSpec {
        name: "H_diag".into(),
        coeff_domain: d.clone(),
        parameters: vec![
            ParamDecl {
                name: "a".into(),
                coeff_domain: d.clone(),
                provenance: None,
            },
            ParamDecl {
                name: "b".into(),
                coeff_domain: d,
                provenance: None,
            },
        ],
        fixed: vec![FixedTarget::SemanticLaw {
            presentation: "M0".into(),
            phase: "Active".into(),
            law: "sem_ok".into(),
        }],
        editable: vec![EditableTarget::RepresentationLaw {
            presentation: "M1".into(),
            phase: "Active".into(),
            law: "repr_extra".into(),
        }],
        provenance: Provenance::new(vec![orig.clone()], vec![MathClause::G140F1]),
    };

    let time_spec = DiagramSpec {
        name: "tri_time".into(),
        direction: MorphismDirection::TimeOrder,
        vertices: vec![
            DiagramVertex {
                name: "v0".into(),
                presentation: p0,
                is_fixed: true,
                provenance: None,
            },
            DiagramVertex {
                name: "v1".into(),
                presentation: p1,
                is_fixed: false,
                provenance: None,
            },
            DiagramVertex {
                name: "v2".into(),
                presentation: p2,
                is_fixed: false,
                provenance: None,
            },
        ],
        edges: vec![
            DiagramEdge {
                name: "f".into(),
                source: "v0".into(),
                target: "v1".into(),
                morphism: apply_cmp_morphism("M1", "M0", PolyExpr::state("x")),
                is_fixed: false,
                provenance: None,
            },
            DiagramEdge {
                name: "g".into(),
                source: "v1".into(),
                target: "v2".into(),
                morphism: apply_cmp_morphism("M2", "M1", PolyExpr::state("x")),
                is_fixed: false,
                provenance: None,
            },
            DiagramEdge {
                name: "h".into(),
                source: "v0".into(),
                target: "v2".into(),
                morphism: apply_cmp_morphism("M2", "M0", PolyExpr::state("x")),
                is_fixed: false,
                provenance: None,
            },
        ],
        relations: vec![DiagramRelation {
            name: "comm".into(),
            lhs: vec!["f".into(), "g".into()],
            rhs: vec!["h".into()],
            provenance: None,
        }],
        change_spec: base_change,
        eval_condition: None,
        edge_eval_conditions: BTreeMap::new(),
        provenance: Provenance::new(vec![orig], vec![MathClause::G140F1Dot2]),
    };
    assert!(CheckedDiagramTask::validate(time_spec.clone()).is_ok());

    let mut bad_fixed_edge = time_spec.clone();
    bad_fixed_edge.edges[0].is_fixed = true;
    assert!(matches!(
        CheckedDiagramTask::validate(bad_fixed_edge),
        Err(ValidationError::ConversionError { .. })
    ));

    let mut bad_sem_edit = time_spec.clone();
    bad_sem_edit
        .change_spec
        .editable
        .push(EditableTarget::RepresentationLaw {
            presentation: "M1".into(),
            phase: "Active".into(),
            law: "sem_ok".into(),
        });
    assert!(matches!(
        CheckedDiagramTask::validate(bad_sem_edit),
        Err(ValidationError::SemanticLawEditable { .. })
    ));

    let mut bad_fixed_edit = time_spec.clone();
    bad_fixed_edit
        .change_spec
        .editable
        .push(EditableTarget::OperationExpr {
            presentation: "M0".into(),
            operation: "apply".into(),
        });
    assert!(matches!(
        CheckedDiagramTask::validate(bad_fixed_edit),
        Err(ValidationError::ConversionError { .. })
    ));

    let mut bad_rel = time_spec.clone();
    bad_rel.relations[0].rhs = vec!["f".into()];
    assert!(matches!(
        CheckedDiagramTask::validate(bad_rel),
        Err(ValidationError::ConversionError { .. })
    ));

    let mut unobs = time_spec;
    unobs.vertices[1].presentation.phases[0]
        .coords
        .push(CoordDecl::missing("m", "D"));
    unobs.vertices[1].presentation.operations[0]
        .updates
        .insert("m".into(), PolyExpr::state("m"));
    unobs.edges[1].morphism.state_comparisons[0]
        .map
        .insert("m".into(), PolyExpr::int(0));
    unobs.edges[0].morphism.word_translation.entries[0].steps[0].arg_exprs[0] =
        PolyExpr::unobserved("edge.arg", None);
    let checked = CheckedDiagramTask::validate(unobs).expect("missing coords allowed in IR");
    let slots = checked.unobserved_slots();
    assert!(slots.contains(&"M1.Active.m".to_owned()));
    assert!(slots.contains(&"edge.arg".to_owned()));
}

#[test]
fn checked_path_task_validation_both_kinds() {
    let orig = origin();
    let d = CoeffDomain::Z;
    let p0 = single_phase_pres("V0", d.clone(), 1);
    let mut p1 = single_phase_pres("V1", d.clone(), 1);
    p1.operations[0].domain_laws.push(StateLaw {
        name: "flag_zero".into(),
        kind: LawKind::Representation,
        polynomial: PolyExpr::param("k") * PolyExpr::state("x"),
        provenance: Some(orig.clone()),
    });

    let edge_v1_v0 = apply_cmp_morphism("V1", "V0", PolyExpr::state("x"));
    let cs = ChangeSpec {
        name: "H_path".into(),
        coeff_domain: d.clone(),
        parameters: vec![ParamDecl {
            name: "k".into(),
            coeff_domain: d,
            provenance: None,
        }],
        fixed: vec![FixedTarget::SemanticLaw {
            presentation: "V0".into(),
            phase: "Active".into(),
            law: "sem_ok".into(),
        }],
        editable: vec![EditableTarget::OperationExpr {
            presentation: "V1".into(),
            operation: "apply".into(),
        }],
        provenance: Provenance::new(vec![orig.clone()], vec![MathClause::G140F2]),
    };

    let fixed_spec = PathSpec {
        name: "change_path".into(),
        kind: PathKind::FixedProtocolChangePath,
        direction: MorphismDirection::TimeOrder,
        query_mode: PathQueryMode::Concatenate {
            first: vec!["r1".into()],
            second: vec!["r_loop".into()],
        },
        length: None,
        vertices: BTreeMap::from([("V0".into(), p0.clone()), ("V1".into(), p1.clone())]),
        rules: vec![
            OneStepRule {
                name: "r1".into(),
                from_vertex: "V0".into(),
                to_vertex: "V1".into(),
                param_guards: vec![NamedPoly::new("g0", PolyExpr::param("k"))],
                param_updates: BTreeMap::from([("k".into(), PolyExpr::int(1))]),
                morphism: edge_v1_v0.clone(),
                eval_condition: None,
                provenance: Some(orig.clone()),
            },
            OneStepRule {
                name: "r_loop".into(),
                from_vertex: "V1".into(),
                to_vertex: "V1".into(),
                param_guards: vec![],
                param_updates: BTreeMap::new(),
                morphism: identity_state_morphism(&p1),
                eval_condition: None,
                provenance: None,
            },
        ],
        start: Some(ModelEndpoint {
            vertex: "V0".into(),
            param_values: BTreeMap::from([("k".into(), ScalarLit::int(0))]),
        }),
        end: Some(ModelEndpoint {
            vertex: "V1".into(),
            param_values: BTreeMap::from([("k".into(), ScalarLit::int(1))]),
        }),
        protocol: None,
        change_spec: cs.clone(),
        eval_condition: None,
        provenance: Provenance::new(vec![orig.clone()], vec![MathClause::G140P5Dot1]),
    };
    assert!(CheckedPathTask::validate(fixed_spec.clone()).is_ok());

    let mut bad_sub = fixed_spec.clone();
    bad_sub.query_mode = PathQueryMode::Subdivide {
        target_edge: identity_state_morphism(&p0),
    };
    assert!(matches!(
        CheckedPathTask::validate(bad_sub),
        Err(ValidationError::ConversionError { .. })
    ));

    let mut bad_sem = fixed_spec;
    bad_sem
        .change_spec
        .editable
        .push(EditableTarget::RepresentationLaw {
            presentation: "V0".into(),
            phase: "Active".into(),
            law: "sem_ok".into(),
        });
    assert!(matches!(
        CheckedPathTask::validate(bad_sem),
        Err(ValidationError::SemanticLawEditable { .. })
    ));

    let enlarged_spec = PathSpec {
        name: "enlarged_exec".into(),
        kind: PathKind::EnlargedProtocolExecutionPath,
        direction: MorphismDirection::TimeOrder,
        query_mode: PathQueryMode::Find,
        length: Some(3),
        vertices: BTreeMap::new(),
        rules: vec![],
        start: None,
        end: None,
        protocol: Some(ProtocolExecutionSpec {
            comparison: edge_v1_v0.to_comparison_pair(&p1, &p0),
            start_phase: "Active".into(),
            start_laws: vec![StateLaw {
                name: "s0".into(),
                kind: LawKind::Representation,
                polynomial: PolyExpr::state("x"),
                provenance: Some(orig.clone()),
            }],
            end_phase: "Active".into(),
            end_laws: vec![StateLaw {
                name: "e0".into(),
                kind: LawKind::Representation,
                polynomial: PolyExpr::unobserved("proto.end", None),
                provenance: Some(orig.clone()),
            }],
            allowed_ops: vec!["apply".into()],
        }),
        change_spec: ChangeSpec {
            fixed: vec![],
            editable: vec![],
            ..cs
        },
        eval_condition: None,
        provenance: Provenance::new(vec![orig], vec![MathClause::G140P5Dot2]),
    };
    let checked_proto = CheckedPathTask::validate(enlarged_spec.clone()).expect("valid protocol");
    assert_eq!(
        checked_proto.unobserved_slots(),
        vec!["proto.end".to_owned()]
    );

    let mut bad_mode = enlarged_spec;
    bad_mode.query_mode = PathQueryMode::Concatenate {
        first: vec![],
        second: vec![],
    };
    assert!(matches!(
        CheckedPathTask::validate(bad_mode),
        Err(ValidationError::ConversionError { .. })
    ));
}

#[test]
fn checked_transfer_task_validation_chain_words_and_errors() {
    let orig = origin();
    let d = CoeffDomain::Z;
    let x0 = single_phase_pres("X0", d.clone(), 1);
    let x1 = single_phase_pres("X1", d.clone(), 1);
    let x2 = single_phase_pres("X2", d.clone(), 1);
    let cmp1 = apply_cmp_morphism("X1", "X0", PolyExpr::state("x")).to_comparison_pair(&x1, &x0);
    let cmp2 = apply_cmp_morphism("X2", "X1", PolyExpr::state("x")).to_comparison_pair(&x2, &x1);

    let transfer_spec = TransferSpec {
        name: "t_chain".into(),
        steps: vec![
            TransferStepSpec {
                name: "s1".into(),
                comparison: cmp1,
                source_phase: "Active".into(),
                domain_laws: vec![StateLaw {
                    name: "d0".into(),
                    kind: LawKind::Representation,
                    polynomial: PolyExpr::state("x"),
                    provenance: Some(orig.clone()),
                }],
                target_phase: "Active".into(),
                lift_map: BTreeMap::from([(
                    "x".into(),
                    PolyExpr::state("x") + PolyExpr::param("p"),
                )]),
                provenance: Some(orig.clone()),
            },
            TransferStepSpec {
                name: "s2".into(),
                comparison: cmp2,
                source_phase: "Active".into(),
                domain_laws: vec![],
                target_phase: "Active".into(),
                lift_map: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
                provenance: None,
            },
        ],
        word_checks: vec![
            WordCheckSpec {
                name: "wc_const".into(),
                args: vec![],
                steps: vec![WordStepExpr {
                    operation: "apply".into(),
                    arg_exprs: vec![PolyExpr::int(1)],
                }],
                provenance: None,
            },
            WordCheckSpec {
                name: "wc_sym".into(),
                args: vec!["u".into()],
                steps: vec![WordStepExpr {
                    operation: "apply".into(),
                    arg_exprs: vec![PolyExpr::arg("u")],
                }],
                provenance: Some(orig.clone()),
            },
        ],
        old_word_lifts: vec![OldWordLiftSpec {
            name: "lift_apply".into(),
            args: vec!["v".into()],
            target_steps: vec![WordStepExpr {
                operation: "apply".into(),
                arg_exprs: vec![PolyExpr::arg("v")],
            }],
            max_length: None,
            provenance: Some(orig.clone()),
        }],
        change_spec: ChangeSpec {
            name: "H_tr".into(),
            coeff_domain: d.clone(),
            parameters: vec![ParamDecl {
                name: "p".into(),
                coeff_domain: d,
                provenance: None,
            }],
            fixed: vec![FixedTarget::SemanticLaw {
                presentation: "X0".into(),
                phase: "Active".into(),
                law: "sem_ok".into(),
            }],
            editable: vec![],
            provenance: Provenance::new(vec![orig.clone()], vec![MathClause::G140G1]),
        },
        eval_condition: None,
        require_full_domain: true,
        provenance: Provenance::new(vec![orig], vec![MathClause::G140G3]),
    };

    assert!(CheckedTransferTask::validate(transfer_spec.clone()).is_ok());

    let mut discont = transfer_spec.clone();
    discont.steps[1].comparison.before = x0;
    assert!(matches!(
        CheckedTransferTask::validate(discont),
        Err(ValidationError::ConversionError { .. })
    ));

    let mut bad_arg = transfer_spec.clone();
    bad_arg.word_checks[0].steps[0].arg_exprs[0] = PolyExpr::arg("undeclared");
    assert!(matches!(
        CheckedTransferTask::validate(bad_arg),
        Err(ValidationError::UnknownRef {
            kind: "operation argument",
            ..
        })
    ));

    let mut bad_dup_arg = transfer_spec.clone();
    bad_dup_arg.word_checks[0].args = vec!["u".into(), "u".into()];
    assert!(matches!(
        CheckedTransferTask::validate(bad_dup_arg),
        Err(ValidationError::DuplicateDecl {
            kind: "word argument",
            ..
        })
    ));

    let mut bad_edit = transfer_spec;
    bad_edit
        .change_spec
        .editable
        .push(EditableTarget::RepresentationLaw {
            presentation: "X2".into(),
            phase: "Active".into(),
            law: "sem_ok".into(),
        });
    assert!(matches!(
        CheckedTransferTask::validate(bad_edit),
        Err(ValidationError::SemanticLawEditable { .. })
    ));
}

#[test]
fn outcome_wire_format_includes_phase2_fields_and_unbounded_silence() {
    let outcome = ShigureOutcome {
        verdict: Verdict::Undetermined(SilenceReason::UnboundedSearchOutOfScope {
            detail: "path length omitted".into(),
        }),
        coeff_domain: CoeffDomain::Z,
        point_domain: PointDomain::AlgebraicClosure,
        applicability: vec![ApplicabilityCheck::failed(
            "bounded_path_length",
            MathClause::G140F2,
            "requires explicit length",
        )],
        provenance: Provenance::new(vec![origin()], vec![MathClause::G140F2]),
        residual_ideal: vec![],
        empty_witness: None,
        restored: None,
        interaction: None,
        diagram: Some(DiagramOutcomeDetail {
            direction: MorphismDirection::TimeOrder,
            commutativity_residuals: BTreeMap::new(),
            structural_mismatches: BTreeMap::new(),
            restored_diagram: None,
        }),
        path: Some(PathOutcomeDetail {
            path_kind: PathOutcomeKind::FixedProtocolChangePath,
            direction: MorphismDirection::TimeOrder,
            query_mode: "find".into(),
            length: None,
            protocol_preservation_verified: None,
            valid_paths: vec![],
            rejected_candidates: vec![],
        }),
        transfer: Some(TransferOutcomeDetail {
            domain_relation: DomainRelation::ProperSubdomain,
            composed_domain_equations: vec!["x".into()],
            step_diagnostics: vec![],
            restored_transfer: None,
            word_checks: vec![],
            old_word_lifts: vec![],
        }),
        robustness: None,
        chevalley: None,
        observations: None,
        lift: None,
        artin: None,
        diagnostics: None,
        atlas: None,
        occurrence: None,
        partial: None,
        revision: None,
        multisource: None,
    };

    let json = outcome.to_json();
    let Json::Obj(map) = &json else {
        panic!("expected Json::Obj");
    };
    assert_eq!(map.get("verdict"), Some(&Json::str("undetermined")));
    assert!(map.contains_key("diagram"));
    assert!(map.contains_key("path"));
    assert!(map.contains_key("transfer"));
    let Some(Json::Obj(silence)) = map.get("silence_reason") else {
        panic!("expected silence_reason");
    };
    assert_eq!(
        silence.get("code"),
        Some(&Json::str("unbounded_search_out_of_scope"))
    );
}
