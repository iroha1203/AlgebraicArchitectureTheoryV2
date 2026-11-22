use super::tests_path::{clit, orig, slit};
use crate::ir::change::{ChangeSpec, EvalCondition, NamedPoly, ParamDecl, PointDomain};
use crate::ir::morphism::{MorphismDirection, StateMorphism};
use crate::ir::path::{
    CheckedPathTask, ModelEndpoint, OneStepRule, PathKind, PathQueryMode, PathSpec,
    ProtocolExecutionSpec,
};
use crate::ir::presentation::{
    ComparisonPair, CoordDecl, LawKind, OperationDecl, PhaseDecl, Presentation, SortDecl,
    StateComparison, StateLaw, TranslatedStep, TranslatedWord, WordTranslation,
};
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::solver::solve_path_task;
use std::collections::BTreeMap;

#[test]
fn path_zero_concatenate_subdivide_f31_and_silence() {
    let q = CoeffDomain::Q;
    let v0 = Presentation {
        name: "P0".into(),
        coeff_domain: q.clone(),
        sorts: vec![SortDecl {
            name: "D".into(),
            rank: 1,
            coeff_domain: q.clone(),
            provenance: Some(orig("d")),
        }],
        phases: vec![PhaseDecl {
            name: "S".into(),
            coords: vec![CoordDecl::symbolic("x", "D")],
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "step".into(),
            source_phase: "S".into(),
            target_phase: "S".into(),
            args: vec![("u".into(), "D".into())],
            domain_laws: vec![],
            updates: BTreeMap::from([("x".into(), PolyExpr::state("x") + PolyExpr::arg("u"))]),
            provenance: None,
        }],
        observations: vec![],
        provenance: Provenance::new(vec![orig("v0")], vec![MathClause::G140F2]),
    };
    let shift_m = |shift: PolyExpr| StateMorphism {
        source: "P0".into(),
        target: "P0".into(),
        state_comparisons: vec![StateComparison {
            after_phase: "S".into(),
            before_phase: "S".into(),
            map: BTreeMap::from([("x".into(), PolyExpr::state("x") + shift)]),
            provenance: None,
        }],
        word_translation: WordTranslation {
            entries: vec![TranslatedWord {
                after_operation: "step".into(),
                steps: vec![TranslatedStep {
                    before_operation: "step".into(),
                    arg_exprs: vec![PolyExpr::arg("u")],
                }],
                provenance: None,
            }],
        },
        provenance: None,
    };

    let r_one = OneStepRule {
        name: "add1".into(),
        from_vertex: "V".into(),
        to_vertex: "V".into(),
        param_guards: vec![],
        param_updates: BTreeMap::new(),
        morphism: shift_m(clit(&q, 1)),
        eval_condition: None,
        provenance: None,
    };
    let concat_spec = PathSpec {
        name: "concat_non_closed".into(),
        kind: PathKind::FixedProtocolChangePath,
        direction: MorphismDirection::StateMap,
        query_mode: PathQueryMode::Concatenate {
            first: vec!["add1".into()],
            second: vec!["add1".into()],
        },
        length: None,
        vertices: BTreeMap::from([("V".into(), v0.clone())]),
        rules: vec![r_one.clone()],
        start: Some(ModelEndpoint {
            vertex: "V".into(),
            param_values: BTreeMap::new(),
        }),
        end: Some(ModelEndpoint {
            vertex: "V".into(),
            param_values: BTreeMap::new(),
        }),
        protocol: None,
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: q.clone(),
            parameters: vec![],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140F2]),
        },
        eval_condition: None,
        provenance: Provenance::new(vec![orig("c")], vec![MathClause::G140F2]),
    };
    let out_c = solve_path_task(&CheckedPathTask::validate(concat_spec).unwrap());
    assert_eq!(out_c.verdict, Verdict::Established);
    assert_eq!(
        out_c.path.unwrap().valid_paths[0].composite_is_one_step,
        Some(false)
    );

    let r_a1 = OneStepRule {
        name: "s1".into(),
        from_vertex: "V".into(),
        to_vertex: "V".into(),
        param_guards: vec![],
        param_updates: BTreeMap::new(),
        morphism: shift_m(PolyExpr::param("a1")),
        eval_condition: None,
        provenance: None,
    };
    let r_a2 = OneStepRule {
        name: "s2".into(),
        from_vertex: "V".into(),
        to_vertex: "V".into(),
        param_guards: vec![],
        param_updates: BTreeMap::new(),
        morphism: shift_m(PolyExpr::param("a2")),
        eval_condition: None,
        provenance: None,
    };
    let sub_spec = PathSpec {
        name: "sub2".into(),
        kind: PathKind::FixedProtocolChangePath,
        direction: MorphismDirection::StateMap,
        query_mode: PathQueryMode::Subdivide {
            target_edge: shift_m(clit(&q, 2)),
        },
        length: Some(2),
        vertices: BTreeMap::from([("V".into(), v0.clone())]),
        rules: vec![r_a1, r_a2],
        start: Some(ModelEndpoint {
            vertex: "V".into(),
            param_values: BTreeMap::new(),
        }),
        end: Some(ModelEndpoint {
            vertex: "V".into(),
            param_values: BTreeMap::new(),
        }),
        protocol: None,
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: q.clone(),
            parameters: vec![
                ParamDecl {
                    name: "a1".into(),
                    coeff_domain: q.clone(),
                    provenance: None,
                },
                ParamDecl {
                    name: "a2".into(),
                    coeff_domain: q.clone(),
                    provenance: None,
                },
            ],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140F3]),
        },
        eval_condition: None,
        provenance: Provenance::new(vec![orig("sub")], vec![MathClause::G140F3]),
    };
    let out_sub = solve_path_task(&CheckedPathTask::validate(sub_spec).unwrap());
    assert_eq!(out_sub.verdict, Verdict::Established);
    assert!(!out_sub.path.unwrap().valid_paths.is_empty());

    let mut bad_target = shift_m(clit(&q, 2));
    bad_target.word_translation.entries[0].steps.clear();
    let bad_sub_spec = PathSpec {
        name: "sub_bad_wt".into(),
        kind: PathKind::FixedProtocolChangePath,
        direction: MorphismDirection::StateMap,
        query_mode: PathQueryMode::Subdivide {
            target_edge: bad_target,
        },
        length: Some(2),
        vertices: BTreeMap::from([("V".into(), v0.clone())]),
        rules: vec![r_one.clone()],
        start: Some(ModelEndpoint {
            vertex: "V".into(),
            param_values: BTreeMap::new(),
        }),
        end: Some(ModelEndpoint {
            vertex: "V".into(),
            param_values: BTreeMap::new(),
        }),
        protocol: None,
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: q.clone(),
            parameters: vec![],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140F3]),
        },
        eval_condition: None,
        provenance: Provenance::new(vec![orig("subbad")], vec![MathClause::G140F3]),
    };
    assert_eq!(
        solve_path_task(&CheckedPathTask::validate(bad_sub_spec).unwrap()).verdict,
        Verdict::Refuted
    );

    let z0_ok = PathSpec {
        name: "zero_ok".into(),
        kind: PathKind::FixedProtocolChangePath,
        direction: MorphismDirection::StateMap,
        query_mode: PathQueryMode::Find,
        length: Some(0),
        vertices: BTreeMap::from([("V".into(), v0.clone())]),
        rules: vec![],
        start: Some(ModelEndpoint {
            vertex: "V".into(),
            param_values: BTreeMap::from([("k".into(), slit(&q, 1))]),
        }),
        end: Some(ModelEndpoint {
            vertex: "V".into(),
            param_values: BTreeMap::from([("k".into(), slit(&q, 1))]),
        }),
        protocol: None,
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
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140F2]),
        },
        eval_condition: None,
        provenance: Provenance::new(vec![orig("z0")], vec![MathClause::G140F2]),
    };
    let out_z0 = solve_path_task(&CheckedPathTask::validate(z0_ok).unwrap());
    assert_eq!(out_z0.verdict, Verdict::Established);
    assert!(out_z0.path.unwrap().valid_paths[0].steps.is_empty());

    let z0_bad = PathSpec {
        name: "zero_bad".into(),
        kind: PathKind::FixedProtocolChangePath,
        direction: MorphismDirection::StateMap,
        query_mode: PathQueryMode::Find,
        length: Some(0),
        vertices: BTreeMap::from([("V".into(), v0.clone())]),
        rules: vec![],
        start: Some(ModelEndpoint {
            vertex: "V".into(),
            param_values: BTreeMap::from([("k".into(), slit(&q, 0))]),
        }),
        end: Some(ModelEndpoint {
            vertex: "V".into(),
            param_values: BTreeMap::from([("k".into(), slit(&q, 1))]),
        }),
        protocol: None,
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
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140F2]),
        },
        eval_condition: None,
        provenance: Provenance::new(vec![orig("z0b")], vec![MathClause::G140F2]),
    };
    assert_eq!(
        solve_path_task(&CheckedPathTask::validate(z0_bad).unwrap()).verdict,
        Verdict::Refuted
    );

    let f31_spec = PathSpec {
        name: "f31_curve_only".into(),
        kind: PathKind::FixedProtocolChangePath,
        direction: MorphismDirection::StateMap,
        query_mode: PathQueryMode::Find,
        length: Some(1),
        vertices: BTreeMap::from([("V".into(), v0.clone())]),
        rules: vec![OneStepRule {
            name: "id".into(),
            from_vertex: "V".into(),
            to_vertex: "V".into(),
            param_guards: vec![],
            param_updates: BTreeMap::new(),
            morphism: shift_m(clit(&q, 0)),
            eval_condition: None,
            provenance: None,
        }],
        start: Some(ModelEndpoint {
            vertex: "V".into(),
            param_values: BTreeMap::from([("k".into(), slit(&q, 0))]),
        }),
        end: Some(ModelEndpoint {
            vertex: "V".into(),
            param_values: BTreeMap::from([("k".into(), slit(&q, 1))]),
        }),
        protocol: None,
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
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140F3Dot1]),
        },
        eval_condition: None,
        provenance: Provenance::new(vec![orig("f31")], vec![MathClause::G140F3Dot1]),
    };
    assert_eq!(
        solve_path_task(&CheckedPathTask::validate(f31_spec).unwrap()).verdict,
        Verdict::Refuted
    );

    let unbounded = CheckedPathTask::validate(PathSpec {
        name: "unbounded".into(),
        kind: PathKind::FixedProtocolChangePath,
        direction: MorphismDirection::StateMap,
        query_mode: PathQueryMode::Find,
        length: None,
        vertices: BTreeMap::from([("V".into(), v0)]),
        rules: vec![r_one],
        start: Some(ModelEndpoint {
            vertex: "V".into(),
            param_values: BTreeMap::new(),
        }),
        end: Some(ModelEndpoint {
            vertex: "V".into(),
            param_values: BTreeMap::new(),
        }),
        protocol: None,
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: q,
            parameters: vec![],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140F2]),
        },
        eval_condition: None,
        provenance: Provenance::new(vec![orig("unb")], vec![MathClause::G140F2]),
    })
    .unwrap();
    let out_unb = solve_path_task(&unbounded);
    assert!(matches!(
        out_unb.verdict,
        Verdict::Undetermined(SilenceReason::UnboundedSearchOutOfScope { .. })
    ));
}

#[test]
fn path_review_regressions_m01_m02_m04() {
    let q = CoeffDomain::Q;
    let z = CoeffDomain::Z;

    // M-01: Z + IntegerPoints + nonlinear start_laws [x^2 - 2] at length 0 must be Undetermined
    let z_pres = Presentation {
        name: "ZPres".into(),
        coeff_domain: z.clone(),
        sorts: vec![SortDecl {
            name: "D".into(),
            rank: 1,
            coeff_domain: z.clone(),
            provenance: Some(orig("d")),
        }],
        phases: vec![PhaseDecl {
            name: "Idle".into(),
            coords: vec![CoordDecl::symbolic("x", "D")],
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "noop".into(),
            source_phase: "Idle".into(),
            target_phase: "Idle".into(),
            args: vec![],
            domain_laws: vec![],
            updates: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
            provenance: None,
        }],
        observations: vec![],
        provenance: Provenance::new(vec![orig("zp")], vec![MathClause::G140P5Dot2]),
    };
    let mut z_after = z_pres.clone();
    z_after.name = "ZPresAfter".into();
    let m01_path = PathSpec {
        name: "m01_z_nl_start_domain".into(),
        kind: PathKind::EnlargedProtocolExecutionPath,
        direction: MorphismDirection::TimeOrder,
        query_mode: PathQueryMode::Find,
        length: Some(0),
        vertices: BTreeMap::new(),
        rules: vec![],
        start: None,
        end: None,
        protocol: Some(ProtocolExecutionSpec {
            comparison: ComparisonPair {
                before: z_pres,
                after: z_after,
                state_comparisons: vec![StateComparison {
                    after_phase: "Idle".into(),
                    before_phase: "Idle".into(),
                    map: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
                    provenance: None,
                }],
                word_translation: WordTranslation {
                    entries: vec![TranslatedWord {
                        after_operation: "noop".into(),
                        steps: vec![],
                        provenance: None,
                    }],
                },
            },
            start_phase: "Idle".into(),
            start_laws: vec![StateLaw {
                name: "x2_2".into(),
                kind: LawKind::Representation,
                polynomial: PolyExpr::pow(PolyExpr::state("x"), 2) - clit(&z, 2),
                provenance: None,
            }],
            end_phase: "Idle".into(),
            end_laws: vec![],
            allowed_ops: vec!["noop".into()],
        }),
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: z.clone(),
            parameters: vec![],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140P5Dot2]),
        },
        eval_condition: Some(EvalCondition {
            name: "intpts".into(),
            evaluations: vec![],
            equations: vec![],
            invertibles: vec![],
            point_domain: PointDomain::IntegerPoints,
            provenance: Provenance::new(vec![orig("intpts")], vec![MathClause::G141D4]),
        }),
        provenance: Provenance::new(vec![orig("m01")], vec![MathClause::G140P5Dot2]),
    };
    assert!(matches!(
        solve_path_task(&CheckedPathTask::validate(m01_path).unwrap()).verdict,
        Verdict::Undetermined(SilenceReason::NonLinearRationalOrIntegerExistence {
            point_domain: PointDomain::IntegerPoints,
            ..
        })
    ));

    // M-02: Concatenate with free param `p` must NOT report composite_is_one_step: true
    // for rules whose updates/guards/invertibles only hold on a strict subset.
    let v_free = Presentation {
        name: "P".into(),
        coeff_domain: q.clone(),
        sorts: vec![SortDecl {
            name: "D".into(),
            rank: 1,
            coeff_domain: q.clone(),
            provenance: Some(orig("d")),
        }],
        phases: vec![PhaseDecl {
            name: "S".into(),
            coords: vec![CoordDecl::symbolic("x", "D")],
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "step".into(),
            source_phase: "S".into(),
            target_phase: "S".into(),
            args: vec![("u".into(), "D".into())],
            domain_laws: vec![],
            updates: BTreeMap::from([("x".into(), PolyExpr::state("x") + PolyExpr::arg("u"))]),
            provenance: None,
        }],
        observations: vec![],
        provenance: Provenance::new(vec![orig("vf")], vec![MathClause::G140F2]),
    };
    let id_m = StateMorphism {
        source: "P".into(),
        target: "P".into(),
        state_comparisons: vec![StateComparison {
            after_phase: "S".into(),
            before_phase: "S".into(),
            map: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
            provenance: None,
        }],
        word_translation: WordTranslation {
            entries: vec![TranslatedWord {
                after_operation: "step".into(),
                steps: vec![TranslatedStep {
                    before_operation: "step".into(),
                    arg_exprs: vec![PolyExpr::arg("u")],
                }],
                provenance: None,
            }],
        },
        provenance: None,
    };
    let r_inc1 = OneStepRule {
        name: "inc1".into(),
        from_vertex: "V".into(),
        to_vertex: "V".into(),
        param_guards: vec![],
        param_updates: BTreeMap::from([("p".into(), PolyExpr::param("p") + clit(&q, 1))]),
        morphism: id_m.clone(),
        eval_condition: None,
        provenance: None,
    };
    let r_narrow_upd = OneStepRule {
        name: "dbl".into(),
        from_vertex: "V".into(),
        to_vertex: "V".into(),
        param_guards: vec![],
        param_updates: BTreeMap::from([("p".into(), clit(&q, 2) * PolyExpr::param("p"))]),
        morphism: id_m.clone(),
        eval_condition: None,
        provenance: None,
    };
    let r_narrow_inv = OneStepRule {
        name: "inv_narrow".into(),
        from_vertex: "V".into(),
        to_vertex: "V".into(),
        param_guards: vec![],
        param_updates: BTreeMap::from([("p".into(), PolyExpr::param("p") + clit(&q, 2))]),
        morphism: id_m.clone(),
        eval_condition: Some(EvalCondition {
            name: "inv_p".into(),
            evaluations: vec![],
            equations: vec![],
            invertibles: vec![NamedPoly {
                name: "p_nz".into(),
                expr: PolyExpr::param("p"),
                provenance: None,
            }],
            point_domain: PointDomain::AlgebraicClosure,
            provenance: Provenance::new(vec![orig("inv_p")], vec![MathClause::G140F2]),
        }),
        provenance: None,
    };
    let concat_free_false = PathSpec {
        name: "concat_free_false".into(),
        kind: PathKind::FixedProtocolChangePath,
        direction: MorphismDirection::StateMap,
        query_mode: PathQueryMode::Concatenate {
            first: vec!["inc1".into()],
            second: vec!["inc1".into()],
        },
        length: None,
        vertices: BTreeMap::from([("V".into(), v_free.clone())]),
        rules: vec![r_inc1.clone(), r_narrow_upd, r_narrow_inv],
        start: Some(ModelEndpoint {
            vertex: "V".into(),
            param_values: BTreeMap::new(),
        }),
        end: Some(ModelEndpoint {
            vertex: "V".into(),
            param_values: BTreeMap::new(),
        }),
        protocol: None,
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: q.clone(),
            parameters: vec![ParamDecl {
                name: "p".into(),
                coeff_domain: q.clone(),
                provenance: None,
            }],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140F2]),
        },
        eval_condition: None,
        provenance: Provenance::new(vec![orig("m02f")], vec![MathClause::G140F2]),
    };
    let out_m02f = solve_path_task(&CheckedPathTask::validate(concat_free_false).unwrap());
    assert_eq!(out_m02f.verdict, Verdict::Established);
    assert_eq!(
        out_m02f.path.unwrap().valid_paths[0].composite_is_one_step,
        Some(false)
    );

    let r_global_add2 = OneStepRule {
        name: "add2".into(),
        from_vertex: "V".into(),
        to_vertex: "V".into(),
        param_guards: vec![],
        param_updates: BTreeMap::from([("p".into(), PolyExpr::param("p") + clit(&q, 2))]),
        morphism: id_m,
        eval_condition: None,
        provenance: None,
    };
    let concat_free_true = PathSpec {
        name: "concat_free_true".into(),
        kind: PathKind::FixedProtocolChangePath,
        direction: MorphismDirection::StateMap,
        query_mode: PathQueryMode::Concatenate {
            first: vec!["inc1".into()],
            second: vec!["inc1".into()],
        },
        length: None,
        vertices: BTreeMap::from([("V".into(), v_free)]),
        rules: vec![r_inc1, r_global_add2],
        start: Some(ModelEndpoint {
            vertex: "V".into(),
            param_values: BTreeMap::new(),
        }),
        end: Some(ModelEndpoint {
            vertex: "V".into(),
            param_values: BTreeMap::new(),
        }),
        protocol: None,
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: q.clone(),
            parameters: vec![ParamDecl {
                name: "p".into(),
                coeff_domain: q.clone(),
                provenance: None,
            }],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140F2]),
        },
        eval_condition: None,
        provenance: Provenance::new(vec![orig("m02t")], vec![MathClause::G140F2]),
    };
    let out_m02t = solve_path_task(&CheckedPathTask::validate(concat_free_true).unwrap());
    assert_eq!(out_m02t.verdict, Verdict::Established);
    assert_eq!(
        out_m02t.path.unwrap().valid_paths[0].composite_is_one_step,
        Some(true)
    );

    // M-04: EnlargedProtocolExecutionPath narrowing free param `a` + parameter-free `before`
    let old_m04 = Presentation {
        name: "OldM04".into(),
        coeff_domain: q.clone(),
        sorts: vec![SortDecl {
            name: "D".into(),
            rank: 1,
            coeff_domain: q.clone(),
            provenance: Some(orig("d")),
        }],
        phases: vec![PhaseDecl {
            name: "Idle".into(),
            coords: vec![CoordDecl::symbolic("x", "D")],
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "apply".into(),
            source_phase: "Idle".into(),
            target_phase: "Idle".into(),
            args: vec![("u".into(), "D".into())],
            domain_laws: vec![],
            updates: BTreeMap::from([("x".into(), PolyExpr::state("x") + PolyExpr::arg("u"))]),
            provenance: None,
        }],
        observations: vec![],
        provenance: Provenance::new(vec![orig("om04")], vec![MathClause::G140P5Dot2]),
    };
    let mut after_m04 = old_m04.clone();
    after_m04.name = "AfterM04".into();
    after_m04.operations.push(OperationDecl {
        name: "noop".into(),
        source_phase: "Idle".into(),
        target_phase: "Idle".into(),
        args: vec![],
        domain_laws: vec![],
        updates: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
        provenance: None,
    });
    let m04_narrow = PathSpec {
        name: "m04_narrow_end_law".into(),
        kind: PathKind::EnlargedProtocolExecutionPath,
        direction: MorphismDirection::TimeOrder,
        query_mode: PathQueryMode::Find,
        length: Some(1),
        vertices: BTreeMap::new(),
        rules: vec![],
        start: None,
        end: None,
        protocol: Some(ProtocolExecutionSpec {
            comparison: ComparisonPair {
                before: old_m04.clone(),
                after: after_m04,
                state_comparisons: vec![StateComparison {
                    after_phase: "Idle".into(),
                    before_phase: "Idle".into(),
                    map: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
                    provenance: None,
                }],
                word_translation: WordTranslation {
                    entries: vec![
                        TranslatedWord {
                            after_operation: "apply".into(),
                            steps: vec![TranslatedStep {
                                before_operation: "apply".into(),
                                arg_exprs: vec![PolyExpr::arg("u")],
                            }],
                            provenance: None,
                        },
                        TranslatedWord {
                            after_operation: "noop".into(),
                            steps: vec![],
                            provenance: None,
                        },
                    ],
                },
            },
            start_phase: "Idle".into(),
            start_laws: vec![],
            end_phase: "Idle".into(),
            end_laws: vec![StateLaw {
                name: "fix_a".into(),
                kind: LawKind::Representation,
                polynomial: PolyExpr::param("a") - clit(&q, 1),
                provenance: None,
            }],
            allowed_ops: vec!["noop".into()],
        }),
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: q.clone(),
            parameters: vec![ParamDecl {
                name: "a".into(),
                coeff_domain: q.clone(),
                provenance: None,
            }],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140P5Dot2]),
        },
        eval_condition: None,
        provenance: Provenance::new(vec![orig("m04n")], vec![MathClause::G140P5Dot2]),
    };
    let out_m04n = solve_path_task(&CheckedPathTask::validate(m04_narrow).unwrap());
    assert_eq!(out_m04n.verdict, Verdict::Established);
    let vp_m04 = &out_m04n.path.unwrap().valid_paths[0];
    assert!(vp_m04.reeval.matched);
    assert_eq!(
        vp_m04.parameter_assignments.get("a").map(String::as_str),
        Some("1")
    );

    let mut bad_before = old_m04;
    bad_before.operations[0].updates.insert(
        "x".into(),
        PolyExpr::state("x") + PolyExpr::param("a") * PolyExpr::arg("u"),
    );
    let mut bad_after = bad_before.clone();
    bad_after.name = "BadAfter".into();
    let m04_param_before = PathSpec {
        name: "m04_param_before".into(),
        kind: PathKind::EnlargedProtocolExecutionPath,
        direction: MorphismDirection::TimeOrder,
        query_mode: PathQueryMode::Find,
        length: Some(0),
        vertices: BTreeMap::new(),
        rules: vec![],
        start: None,
        end: None,
        protocol: Some(ProtocolExecutionSpec {
            comparison: ComparisonPair {
                before: bad_before,
                after: bad_after,
                state_comparisons: vec![StateComparison {
                    after_phase: "Idle".into(),
                    before_phase: "Idle".into(),
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
            },
            start_phase: "Idle".into(),
            start_laws: vec![],
            end_phase: "Idle".into(),
            end_laws: vec![],
            allowed_ops: vec!["apply".into()],
        }),
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: q,
            parameters: vec![ParamDecl {
                name: "a".into(),
                coeff_domain: CoeffDomain::Q,
                provenance: None,
            }],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140E1E2]),
        },
        eval_condition: None,
        provenance: Provenance::new(vec![orig("m04b")], vec![MathClause::G140E1E2]),
    };
    assert!(matches!(
        solve_path_task(&CheckedPathTask::validate(m04_param_before).unwrap()).verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { ref condition, .. })
            if condition == "before_presentation_must_be_parameter_free"
    ));
}
