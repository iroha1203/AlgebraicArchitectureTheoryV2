use super::tests_path::{clit, orig, slit};
use crate::ir::change::{ChangeSpec, ParamDecl};
use crate::ir::morphism::{MorphismDirection, StateMorphism};
use crate::ir::path::{
    CheckedPathTask, ModelEndpoint, OneStepRule, PathKind, PathQueryMode, PathSpec,
};
use crate::ir::presentation::{
    CoordDecl, OperationDecl, PhaseDecl, Presentation, SortDecl, StateComparison, TranslatedStep,
    TranslatedWord, WordTranslation,
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
