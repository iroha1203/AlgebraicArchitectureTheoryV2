use super::*;
use crate::solver::{ShigureQueryKind, execute_shigure_task};
use std::collections::BTreeMap;

fn origin() -> SourceRef {
    SourceRef::new("phase2-review-reg", OriginKind::HumanAdopted).with_location(
        "unit-test",
        "reg.law",
        Some((1, 10)),
    )
}

fn base_pres(name: &str) -> Presentation {
    let orig = origin();
    Presentation {
        name: name.into(),
        coeff_domain: CoeffDomain::Z,
        sorts: vec![SortDecl {
            name: "D".into(),
            rank: 1,
            coeff_domain: CoeffDomain::Z,
            provenance: Some(orig.clone()),
        }],
        phases: vec![PhaseDecl {
            name: "Active".into(),
            coords: vec![CoordDecl::symbolic("x", "D")],
            state_laws: vec![StateLaw {
                name: "sem_ok".into(),
                kind: LawKind::Semantic,
                polynomial: PolyExpr::int(0),
                provenance: None,
            }],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "apply".into(),
            source_phase: "Active".into(),
            target_phase: "Active".into(),
            args: vec![("u".into(), "D".into())],
            domain_laws: vec![],
            updates: BTreeMap::from([("x".into(), PolyExpr::state("x") + PolyExpr::arg("u"))]),
            provenance: None,
        }],
        observations: vec![ObservationDecl {
            name: "read".into(),
            phase: "Active".into(),
            components: vec![PolyExpr::state("x")],
            provenance: None,
        }],
        provenance: Provenance::new(vec![orig], vec![MathClause::G140F1]),
    }
}

fn id_edge(src: &str, tgt: &str) -> StateMorphism {
    StateMorphism {
        source: src.into(),
        target: tgt.into(),
        state_comparisons: vec![StateComparison {
            after_phase: "Active".into(),
            before_phase: "Active".into(),
            map: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
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

fn empty_change(name: &str, params: Vec<&str>) -> ChangeSpec {
    ChangeSpec {
        name: name.into(),
        coeff_domain: CoeffDomain::Z,
        parameters: params
            .into_iter()
            .map(|p| ParamDecl {
                name: p.into(),
                coeff_domain: CoeffDomain::Z,
                provenance: None,
            })
            .collect(),
        fixed: vec![],
        editable: vec![],
        provenance: Provenance::new(vec![origin()], vec![MathClause::G140F2]),
    }
}

#[test]
fn f1_enlarged_protocol_unobserved_in_comparison_h_and_tau_collected() {
    let before = base_pres("P0");
    let after = base_pres("P1");
    let mut cmp = id_edge("P1", "P0").to_comparison_pair(&after, &before);
    cmp.state_comparisons[0]
        .map
        .insert("x".into(), PolyExpr::unobserved("cmp.h.x", None));
    cmp.word_translation.entries[0].steps[0].arg_exprs[0] = PolyExpr::unobserved("cmp.tau.u", None);

    let spec = PathSpec {
        name: "f1_unobs".into(),
        kind: PathKind::EnlargedProtocolExecutionPath,
        direction: MorphismDirection::TimeOrder,
        query_mode: PathQueryMode::Find,
        length: Some(1),
        vertices: BTreeMap::new(),
        rules: vec![],
        start: None,
        end: None,
        protocol: Some(ProtocolExecutionSpec {
            comparison: cmp,
            start_phase: "Active".into(),
            start_laws: vec![],
            end_phase: "Active".into(),
            end_laws: vec![],
            allowed_ops: vec!["apply".into()],
        }),
        change_spec: empty_change("H", vec![]),
        eval_condition: None,
        provenance: Provenance::new(vec![origin()], vec![MathClause::G140P5Dot2]),
    };

    let checked = CheckedPathTask::validate(spec).expect("valid enlarged path with unobserved");
    let slots = checked.unobserved_slots();
    assert_eq!(slots, vec!["cmp.h.x".to_owned(), "cmp.tau.u".to_owned()]);
}

#[test]
fn f2_operation_domain_laws_participate_in_preservation_and_param_free_check() {
    let mut before = base_pres("BeforeDL");
    let after = base_pres("AfterDL");

    // 1. after 側の domain_laws が src_laws に組み込まれ、保存判定に効くことを Z + AlgebraicClosure で確認
    let mut after_need_dl = after.clone();
    after_need_dl.phases[0].state_laws.push(StateLaw {
        name: "x_must_stay_zero_after".into(),
        kind: LawKind::Representation,
        polynomial: PolyExpr::state("x"),
        provenance: None,
    });
    let mut pair_no_dl = id_edge("AfterDL", "BeforeDL").to_comparison_pair(&after_need_dl, &before);
    // before は x 任意で apply が x->x+u。after の apply に y->y+x（y=0 が不変条件）を追加すると、
    // after.domain_laws が空なら y=0 閉性が破れ Refuted、domain_laws:[x] があれば Established。
    pair_no_dl.after.phases[0].state_laws.pop();
    pair_no_dl.after.phases[0]
        .coords
        .push(CoordDecl::symbolic("y", "D"));
    pair_no_dl.after.phases[0].state_laws.push(StateLaw {
        name: "y_zero".into(),
        kind: LawKind::Representation,
        polynomial: PolyExpr::state("y"),
        provenance: None,
    });
    pair_no_dl.after.operations[0]
        .updates
        .insert("y".into(), PolyExpr::state("y") + PolyExpr::state("x"));

    let cond_closure = EvalCondition {
        name: "closure".into(),
        evaluations: vec![],
        equations: vec![],
        invertibles: vec![],
        point_domain: PointDomain::AlgebraicClosure,
        provenance: Provenance::new(vec![origin()], vec![MathClause::G140G2]),
    };

    let task_without_dl = CheckedShigureTask::validate(
        pair_no_dl.clone(),
        empty_change("H", vec![]),
        Some(cond_closure.clone()),
    )
    .expect("valid task without dl");
    let out_without =
        execute_shigure_task(&task_without_dl, ShigureQueryKind::ConditionalSolutionSpace);
    assert_eq!(out_without.verdict, Verdict::Refuted);

    let mut pair_with_dl = pair_no_dl;
    pair_with_dl.after.operations[0].domain_laws.push(StateLaw {
        name: "pre_x_zero".into(),
        kind: LawKind::Representation,
        polynomial: PolyExpr::state("x"),
        provenance: None,
    });
    let task_with_dl = CheckedShigureTask::validate(
        pair_with_dl,
        empty_change("H", vec![]),
        Some(cond_closure.clone()),
    )
    .expect("valid task with after domain_laws");
    let out_with = execute_shigure_task(&task_with_dl, ShigureQueryKind::ConditionalSolutionSpace);
    assert_eq!(out_with.verdict, Verdict::Established);

    // 1b. before 側の操作 domain_laws の引き戻しも after.domain_laws なしで Refuted・ありで Established
    let mut before_with_dl = before.clone();
    before_with_dl.operations[0].domain_laws.push(StateLaw {
        name: "before_req_x_zero".into(),
        kind: LawKind::Semantic,
        polynomial: PolyExpr::state("x"),
        provenance: None,
    });
    let mut after_pullback = after.clone();
    let pair_pb_fail =
        id_edge("AfterDL", "BeforeDL").to_comparison_pair(&after_pullback, &before_with_dl);
    let task_pb_fail = CheckedShigureTask::validate(
        pair_pb_fail,
        empty_change("H", vec![]),
        Some(cond_closure.clone()),
    )
    .expect("valid task for before domain pullback failure");
    assert_eq!(
        execute_shigure_task(&task_pb_fail, ShigureQueryKind::ConditionalSolutionSpace).verdict,
        Verdict::Refuted
    );
    after_pullback.operations[0].domain_laws.push(StateLaw {
        name: "after_req_x_zero".into(),
        kind: LawKind::Representation,
        polynomial: PolyExpr::state("x"),
        provenance: None,
    });
    let pair_pb_ok =
        id_edge("AfterDL", "BeforeDL").to_comparison_pair(&after_pullback, &before_with_dl);
    let task_pb_ok =
        CheckedShigureTask::validate(pair_pb_ok, empty_change("H", vec![]), Some(cond_closure))
            .expect("valid task for before domain pullback match");
    assert_eq!(
        execute_shigure_task(&task_pb_ok, ShigureQueryKind::ConditionalSolutionSpace).verdict,
        Verdict::Established
    );

    // 2. before 側の domain_laws に ParamVar が含まれる場合もパラメータフリー検査で沈黙する
    before.operations[0].domain_laws.push(StateLaw {
        name: "bad_before_dl".into(),
        kind: LawKind::Representation,
        polynomial: PolyExpr::param("k") * PolyExpr::state("x"),
        provenance: None,
    });
    let pair_p = id_edge("AfterDL", "BeforeDL").to_comparison_pair(&after, &before);
    let task_p = CheckedShigureTask::validate(pair_p, empty_change("H", vec!["k"]), None)
        .expect("IR validates");
    let out_p = execute_shigure_task(&task_p, ShigureQueryKind::SemanticPreservation);
    assert!(matches!(
        out_p.verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { ref condition, .. })
        if condition == "before_presentation_must_be_parameter_free"
    ));
}

#[test]
fn f3_enlarged_protocol_rejects_unused_vertices_or_endpoints() {
    let before = base_pres("P0");
    let after = base_pres("P1");
    let mut spec = PathSpec {
        name: "f3_unused".into(),
        kind: PathKind::EnlargedProtocolExecutionPath,
        direction: MorphismDirection::TimeOrder,
        query_mode: PathQueryMode::Find,
        length: Some(1),
        vertices: BTreeMap::from([("V0".into(), before.clone())]),
        rules: vec![],
        start: None,
        end: None,
        protocol: Some(ProtocolExecutionSpec {
            comparison: id_edge("P1", "P0").to_comparison_pair(&after, &before),
            start_phase: "Active".into(),
            start_laws: vec![],
            end_phase: "Active".into(),
            end_laws: vec![],
            allowed_ops: vec!["apply".into()],
        }),
        change_spec: empty_change("H", vec![]),
        eval_condition: None,
        provenance: Provenance::new(vec![origin()], vec![MathClause::G140P5Dot2]),
    };

    assert!(matches!(
        CheckedPathTask::validate(spec.clone()),
        Err(ValidationError::ConversionError { .. })
    ));

    spec.vertices.clear();
    spec.start = Some(ModelEndpoint {
        vertex: "V0".into(),
        param_values: BTreeMap::new(),
    });
    assert!(matches!(
        CheckedPathTask::validate(spec),
        Err(ValidationError::ConversionError { .. })
    ));
}

#[test]
fn f4_shared_presentation_name_cannot_bypass_fixed_or_semantic_law_protection() {
    let p0 = base_pres("Shared");
    let mut p0_diff = base_pres("Shared");
    p0_diff.phases[0].state_laws.push(StateLaw {
        name: "extra".into(),
        kind: LawKind::Representation,
        polynomial: PolyExpr::state("x"),
        provenance: None,
    });

    // 同一名かつ同一内容でも固定頂点が1つでもあれば editable を拒否
    let mut cs_op = empty_change("H_shared", vec![]);
    cs_op.editable.push(EditableTarget::OperationExpr {
        presentation: "Shared".into(),
        operation: "apply".into(),
    });
    let diag_same = DiagramSpec {
        name: "dup_name".into(),
        direction: MorphismDirection::TimeOrder,
        vertices: vec![
            DiagramVertex {
                name: "v0".into(),
                presentation: p0.clone(),
                is_fixed: true,
                provenance: None,
            },
            DiagramVertex {
                name: "v1".into(),
                presentation: p0.clone(),
                is_fixed: false,
                provenance: None,
            },
        ],
        edges: vec![],
        relations: vec![],
        change_spec: cs_op,
        eval_condition: None,
        edge_eval_conditions: BTreeMap::new(),
        provenance: Provenance::new(vec![origin()], vec![MathClause::G140F1]),
    };
    assert!(matches!(
        CheckedDiagramTask::validate(diag_same.clone()),
        Err(ValidationError::ConversionError { .. })
    ));

    // 同一 presentation.name を異なる Presentation 定義で再利用する図式も拒否
    let mut diag_diff = diag_same;
    diag_diff.change_spec.editable.clear();
    diag_diff.vertices[1].presentation = p0_diff;
    assert!(matches!(
        CheckedDiagramTask::validate(diag_diff),
        Err(ValidationError::ConversionError { .. })
    ));
}

#[test]
fn f5_compose_time_order_checks_middle_and_after_presentation_names() {
    let p0 = base_pres("M0");
    let p1 = base_pres("M1");
    let p2 = base_pres("M2");
    let wrong = base_pres("Wrong");

    let t1 = TimeStepMorphism::new("M0", "M1", id_edge("M1", "M0")).unwrap();
    let t2 = TimeStepMorphism::new("M1", "M2", id_edge("M2", "M1")).unwrap();
    assert!(matches!(
        compose_time_order(&t1, &t2, &wrong, &p2),
        Err(ValidationError::ConversionError { .. })
    ));
    assert!(matches!(
        compose_time_order(&t1, &t2, &p1, &wrong),
        Err(ValidationError::ConversionError { .. })
    ));
    assert!(compose_time_order(&t1, &t2, &p1, &p2).is_ok());
    let _ = p0;
}

#[test]
fn f6_source_ref_and_duplicate_name_checks_on_diagram_and_path_fields() {
    let p0 = base_pres("D0");
    let bad_ref = Some(SourceRef::new("", OriginKind::HumanAdopted));
    let base_diag = DiagramSpec {
        name: "f6_diag".into(),
        direction: MorphismDirection::TimeOrder,
        vertices: vec![DiagramVertex {
            name: "v0".into(),
            presentation: p0.clone(),
            is_fixed: false,
            provenance: bad_ref.clone(),
        }],
        edges: vec![],
        relations: vec![],
        change_spec: empty_change("H", vec![]),
        eval_condition: None,
        edge_eval_conditions: BTreeMap::new(),
        provenance: Provenance::new(vec![origin()], vec![MathClause::G140F1]),
    };
    assert!(matches!(
        CheckedDiagramTask::validate(base_diag.clone()),
        Err(ValidationError::EmptyName { .. })
    ));

    let mut bad_edge = base_diag.clone();
    bad_edge.vertices[0].provenance = None;
    bad_edge.edges.push(DiagramEdge {
        name: "e".into(),
        source: "v0".into(),
        target: "v0".into(),
        morphism: id_edge("D0", "D0"),
        is_fixed: false,
        provenance: bad_ref.clone(),
    });
    assert!(matches!(
        CheckedDiagramTask::validate(bad_edge),
        Err(ValidationError::EmptyName { .. })
    ));

    let mut bad_rel = base_diag;
    bad_rel.vertices[0].provenance = None;
    bad_rel.edges.push(DiagramEdge {
        name: "e".into(),
        source: "v0".into(),
        target: "v0".into(),
        morphism: id_edge("D0", "D0"),
        is_fixed: false,
        provenance: None,
    });
    bad_rel.relations.push(DiagramRelation {
        name: "r".into(),
        lhs: vec!["e".into()],
        rhs: vec!["e".into()],
        provenance: bad_ref,
    });
    assert!(matches!(
        CheckedDiagramTask::validate(bad_rel),
        Err(ValidationError::EmptyName { .. })
    ));

    // Path param_guards duplicate & bad provenance
    let ep = ModelEndpoint {
        vertex: "v0".into(),
        param_values: BTreeMap::new(),
    };
    let bad_path = PathSpec {
        name: "f6_path".into(),
        kind: PathKind::FixedProtocolChangePath,
        direction: MorphismDirection::TimeOrder,
        query_mode: PathQueryMode::Find,
        length: Some(1),
        vertices: BTreeMap::from([("v0".into(), p0)]),
        rules: vec![OneStepRule {
            name: "step".into(),
            from_vertex: "v0".into(),
            to_vertex: "v0".into(),
            param_guards: vec![
                NamedPoly::new("g", PolyExpr::int(0)),
                NamedPoly::new("g", PolyExpr::int(0)),
            ],
            param_updates: BTreeMap::new(),
            morphism: id_edge("D0", "D0"),
            eval_condition: None,
            provenance: None,
        }],
        start: Some(ep.clone()),
        end: Some(ep),
        protocol: None,
        change_spec: empty_change("H", vec![]),
        eval_condition: None,
        provenance: Provenance::new(vec![origin()], vec![MathClause::G140F2]),
    };
    assert!(matches!(
        CheckedPathTask::validate(bad_path),
        Err(ValidationError::DuplicateDecl {
            kind: "param guard",
            ..
        })
    ));
}

#[test]
fn f7_compose_state_order_rejects_broken_middle_phase_chain() {
    let p_src = base_pres("Src");
    let mut p_mid = base_pres("Mid");
    p_mid.phases.push(PhaseDecl {
        name: "Other".into(),
        coords: vec![CoordDecl::symbolic("x", "D")],
        state_laws: vec![],
        provenance: None,
    });
    p_mid.operations[0].source_phase = "Other".into();
    let p_tgt = base_pres("Tgt");

    let inner = id_edge("Src", "Mid");
    let mut outer = id_edge("Mid", "Tgt");
    outer.state_comparisons.push(StateComparison {
        after_phase: "Other".into(),
        before_phase: "Active".into(),
        map: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
        provenance: None,
    });

    // inner maps Active -> Active, but middle's `apply` expects source_phase `Other`
    assert!(matches!(
        compose_state_order(&outer, &inner, &p_src, &p_mid),
        Err(ValidationError::PhasePathMismatch { .. })
    ));
    let _ = p_tgt;
}
