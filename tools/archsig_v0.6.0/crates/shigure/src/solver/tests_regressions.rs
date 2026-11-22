use super::*;
use crate::ir::change::{ChangeSpec, EvalCondition, NamedPoly, ParamDecl, PointDomain};
use crate::ir::presentation::{
    ComparisonPair, CoordDecl, LawKind, ObservationDecl, OperationDecl, PhaseDecl, Presentation,
    SortDecl, StateComparison, StateLaw, TranslatedStep, TranslatedWord, WordTranslation,
};
use crate::ir::provenance::Provenance;
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::ir::validate::CheckedShigureTask;
use crate::solver::tests::{build_single_param_residual_task, q_lit, single_ledger_before};
use num_bigint::BigUint;
use std::collections::BTreeMap;

#[test]
fn rerun1_f1_nilpotent_interaction_f2_implicit_open_f3_real_witness_f4_domain_and_f6_free_params() {
    // 1. F1 回帰: 冪零元感受性のある状態 Law `a^2 * y = 0`・観測 `x + a*(y + b*x)` は
    //    Q[ε]/(ε^2) で破綻するため InteractionAnalysis (UniversalRing) で沈黙する。
    let before_q = single_ledger_before(CoeffDomain::Q);
    let after_nilp = Presentation {
        name: "NilpotentQuot".to_owned(),
        coeff_domain: CoeffDomain::Q,
        sorts: vec![SortDecl {
            name: "D".to_owned(),
            rank: 1,
            coeff_domain: CoeffDomain::Q,
            provenance: None,
        }],
        phases: vec![PhaseDecl {
            name: "Active".to_owned(),
            coords: vec![CoordDecl::symbolic("x", "D"), CoordDecl::symbolic("y", "D")],
            state_laws: vec![StateLaw {
                name: "a2_y_zero".to_owned(),
                kind: LawKind::Representation,
                polynomial: PolyExpr::pow(PolyExpr::param("a"), 2) * PolyExpr::state("y"),
                provenance: None,
            }],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "apply".to_owned(),
            source_phase: "Active".to_owned(),
            target_phase: "Active".to_owned(),
            args: vec![("u".to_owned(), "D".to_owned())],
            domain_laws: vec![],
            updates: BTreeMap::from([
                ("x".to_owned(), PolyExpr::state("x") + PolyExpr::arg("u")),
                ("y".to_owned(), PolyExpr::state("y")),
            ]),
            provenance: None,
        }],
        observations: vec![ObservationDecl {
            name: "read".to_owned(),
            phase: "Active".to_owned(),
            components: vec![
                PolyExpr::state("x")
                    + PolyExpr::param("a")
                        * (PolyExpr::state("y") + PolyExpr::param("b") * PolyExpr::state("x")),
            ],
            provenance: None,
        }],
        provenance: Provenance::default(),
    };
    let task_nilp = CheckedShigureTask::validate(
        ComparisonPair {
            before: before_q,
            after: after_nilp,
            state_comparisons: vec![StateComparison {
                after_phase: "Active".to_owned(),
                before_phase: "Active".to_owned(),
                map: BTreeMap::from([("x".to_owned(), PolyExpr::state("x"))]),
                provenance: None,
            }],
            word_translation: WordTranslation {
                entries: vec![TranslatedWord {
                    after_operation: "apply".to_owned(),
                    steps: vec![TranslatedStep {
                        before_operation: "apply".to_owned(),
                        arg_exprs: vec![PolyExpr::arg("u")],
                    }],
                    provenance: None,
                }],
            },
        },
        ChangeSpec {
            name: "H_nilp".to_owned(),
            coeff_domain: CoeffDomain::Q,
            parameters: vec![
                ParamDecl {
                    name: "a".to_owned(),
                    coeff_domain: CoeffDomain::Q,
                    provenance: None,
                },
                ParamDecl {
                    name: "b".to_owned(),
                    coeff_domain: CoeffDomain::Q,
                    provenance: None,
                },
            ],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::default(),
        },
        None,
    )
    .unwrap();
    assert!(matches!(
        execute_shigure_task(&task_nilp, ShigureQueryKind::InteractionAnalysis).verdict,
        Verdict::Undetermined(SilenceReason::QuotientIdealOutOfScope { .. })
    ));

    // 2. F2 回帰: 単一非閉商環層 `a*y = 0, read = x + y`（真ローカスは D(a)）は
    //    eval_condition なしでは開条件 D(a) を黙って落とさず QuotientIdealOutOfScope で沈黙し、
    //    D(a) を明示した eval_condition 付きなら Established となる。
    let build_oq = |eval: Option<EvalCondition>| {
        let before = single_ledger_before(CoeffDomain::Q);
        let after = Presentation {
            name: "SingleOpenQuot".to_owned(),
            coeff_domain: CoeffDomain::Q,
            sorts: vec![SortDecl {
                name: "D".to_owned(),
                rank: 1,
                coeff_domain: CoeffDomain::Q,
                provenance: None,
            }],
            phases: vec![PhaseDecl {
                name: "Active".to_owned(),
                coords: vec![CoordDecl::symbolic("x", "D"), CoordDecl::symbolic("y", "D")],
                state_laws: vec![StateLaw {
                    name: "ay_zero".to_owned(),
                    kind: LawKind::Representation,
                    polynomial: PolyExpr::param("a") * PolyExpr::state("y"),
                    provenance: None,
                }],
                provenance: None,
            }],
            operations: vec![OperationDecl {
                name: "apply".to_owned(),
                source_phase: "Active".to_owned(),
                target_phase: "Active".to_owned(),
                args: vec![("u".to_owned(), "D".to_owned())],
                domain_laws: vec![],
                updates: BTreeMap::from([
                    ("x".to_owned(), PolyExpr::state("x") + PolyExpr::arg("u")),
                    ("y".to_owned(), PolyExpr::state("y")),
                ]),
                provenance: None,
            }],
            observations: vec![ObservationDecl {
                name: "read".to_owned(),
                phase: "Active".to_owned(),
                components: vec![PolyExpr::state("x") + PolyExpr::state("y")],
                provenance: None,
            }],
            provenance: Provenance::default(),
        };
        CheckedShigureTask::validate(
            ComparisonPair {
                before,
                after,
                state_comparisons: vec![StateComparison {
                    after_phase: "Active".to_owned(),
                    before_phase: "Active".to_owned(),
                    map: BTreeMap::from([("x".to_owned(), PolyExpr::state("x"))]),
                    provenance: None,
                }],
                word_translation: WordTranslation {
                    entries: vec![TranslatedWord {
                        after_operation: "apply".to_owned(),
                        steps: vec![TranslatedStep {
                            before_operation: "apply".to_owned(),
                            arg_exprs: vec![PolyExpr::arg("u")],
                        }],
                        provenance: None,
                    }],
                },
            },
            ChangeSpec {
                name: "H_oq_f2".to_owned(),
                coeff_domain: CoeffDomain::Q,
                parameters: vec![ParamDecl {
                    name: "a".to_owned(),
                    coeff_domain: CoeffDomain::Q,
                    provenance: None,
                }],
                fixed: vec![],
                editable: vec![],
                provenance: Provenance::default(),
            },
            eval,
        )
        .unwrap()
    };
    let task_oq_none = build_oq(None);
    assert!(matches!(
        execute_shigure_task(&task_oq_none, ShigureQueryKind::SemanticPreservation).verdict,
        Verdict::Undetermined(SilenceReason::QuotientIdealOutOfScope { .. })
    ));
    assert!(matches!(
        execute_shigure_task(&task_oq_none, ShigureQueryKind::ConditionalSolutionSpace).verdict,
        Verdict::Undetermined(SilenceReason::QuotientIdealOutOfScope { .. })
    ));
    let task_oq_explicit = build_oq(Some(EvalCondition {
        name: "explicit_D_a".to_owned(),
        evaluations: vec![],
        equations: vec![],
        invertibles: vec![NamedPoly::new("a_unit", PolyExpr::param("a"))],
        point_domain: PointDomain::AlgebraicClosure,
        provenance: Provenance::default(),
    }));
    let out_oq_ok = execute_shigure_task(
        &task_oq_explicit,
        ShigureQueryKind::ConditionalSolutionSpace,
    );
    assert_eq!(out_oq_ok.verdict, Verdict::Established);
    assert!(
        out_oq_ok
            .restored
            .expect("restored under D(a)")
            .reeval
            .matched
    );

    // 3. F3 回帰: ambient 残差 `a - 1 = 0, a - 2 = 0` が直接矛盾するとき、
    //    空性 witness はトートロジー ["1"] ではなく実残差生成元を保持して検算一致する。
    let before_inc = single_ledger_before(CoeffDomain::Q);
    let after_inc = Presentation {
        name: "InconsistentAmbient".to_owned(),
        coeff_domain: CoeffDomain::Q,
        sorts: vec![SortDecl {
            name: "D".to_owned(),
            rank: 1,
            coeff_domain: CoeffDomain::Q,
            provenance: None,
        }],
        phases: vec![PhaseDecl {
            name: "Active".to_owned(),
            coords: vec![CoordDecl::symbolic("x", "D")],
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "apply".to_owned(),
            source_phase: "Active".to_owned(),
            target_phase: "Active".to_owned(),
            args: vec![("u".to_owned(), "D".to_owned())],
            domain_laws: vec![],
            updates: BTreeMap::from([(
                "x".to_owned(),
                PolyExpr::state("x")
                    + PolyExpr::arg("u")
                    + (PolyExpr::param("a") - q_lit(1)) * PolyExpr::state("x")
                    + (PolyExpr::param("a") - q_lit(2)),
            )]),
            provenance: None,
        }],
        observations: vec![ObservationDecl {
            name: "read".to_owned(),
            phase: "Active".to_owned(),
            components: vec![PolyExpr::state("x")],
            provenance: None,
        }],
        provenance: Provenance::default(),
    };
    let task_inc = CheckedShigureTask::validate(
        ComparisonPair {
            before: before_inc,
            after: after_inc,
            state_comparisons: vec![StateComparison {
                after_phase: "Active".to_owned(),
                before_phase: "Active".to_owned(),
                map: BTreeMap::from([("x".to_owned(), PolyExpr::state("x"))]),
                provenance: None,
            }],
            word_translation: WordTranslation {
                entries: vec![TranslatedWord {
                    after_operation: "apply".to_owned(),
                    steps: vec![TranslatedStep {
                        before_operation: "apply".to_owned(),
                        arg_exprs: vec![PolyExpr::arg("u")],
                    }],
                    provenance: None,
                }],
            },
        },
        ChangeSpec {
            name: "H_inc".to_owned(),
            coeff_domain: CoeffDomain::Q,
            parameters: vec![ParamDecl {
                name: "a".to_owned(),
                coeff_domain: CoeffDomain::Q,
                provenance: None,
            }],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::default(),
        },
        None,
    )
    .unwrap();
    let out_inc = execute_shigure_task(&task_inc, ShigureQueryKind::SemanticPreservation);
    assert_eq!(out_inc.verdict, Verdict::Refuted);
    let witness = out_inc.empty_witness.expect("real empty witness");
    assert!(witness.verified);
    assert!(witness.generators.contains(&"a - 1".to_owned()));
    assert!(witness.generators.contains(&"a - 2".to_owned()));
    assert_ne!(witness.generators, vec!["1".to_owned()]);

    // 4. F4 回帰: Fp(5) の t^5 - t に point_domain = Fp(5)_points を指定した InteractionAnalysis は
    //    UniversalRing 違反として fail-closed に沈黙する。
    let p5 = BigUint::from(5u32);
    let task_fp_inter = build_single_param_residual_task(
        CoeffDomain::Fp(p5.clone()),
        "t",
        PolyExpr::pow(PolyExpr::param("t"), 5) - PolyExpr::param("t"),
        Some(EvalCondition {
            name: "fp5_interaction_mismatch".to_owned(),
            evaluations: vec![],
            equations: vec![],
            invertibles: vec![],
            point_domain: PointDomain::FiniteFieldPoints(p5),
            provenance: Provenance::default(),
        }),
    );
    assert!(matches!(
        execute_shigure_task(&task_fp_inter, ShigureQueryKind::InteractionAnalysis).verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet {
            ref condition,
            ..
        }) if condition == "universal_ring_required_for_interaction"
    ));

    // 5. F6 回帰: 非線形制約 `k^2 + 1 = 0`（AlgebraicClosure）では k は free_parameters に含まれない。
    let out_f6 = execute_shigure_task(
        &build_single_param_residual_task(
            CoeffDomain::Q,
            "k",
            PolyExpr::pow(PolyExpr::param("k"), 2) + q_lit(1),
            None,
        ),
        ShigureQueryKind::ConditionalSolutionSpace,
    );
    assert_eq!(out_f6.verdict, Verdict::Established);
    let rest_f6 = out_f6.restored.expect("restored closure");
    assert!(rest_f6.free_parameters.is_empty());

    // 6. 境界検査: before 側へ ParamVar が混入したタスクは fail-closed で沈黙。
    let mut before_param = single_ledger_before(CoeffDomain::Q);
    before_param.observations[0].components[0] = PolyExpr::state("x") + PolyExpr::param("c");
    let mut after_bp = single_ledger_before(CoeffDomain::Q);
    after_bp.name = "AfterBP".to_owned();
    let task_bp = CheckedShigureTask::validate(
        ComparisonPair {
            before: before_param,
            after: after_bp,
            state_comparisons: vec![StateComparison {
                after_phase: "Active".to_owned(),
                before_phase: "Active".to_owned(),
                map: BTreeMap::from([("x".to_owned(), PolyExpr::state("x"))]),
                provenance: None,
            }],
            word_translation: WordTranslation {
                entries: vec![TranslatedWord {
                    after_operation: "apply".to_owned(),
                    steps: vec![TranslatedStep {
                        before_operation: "apply".to_owned(),
                        arg_exprs: vec![PolyExpr::arg("u")],
                    }],
                    provenance: None,
                }],
            },
        },
        ChangeSpec {
            name: "H_bp".to_owned(),
            coeff_domain: CoeffDomain::Q,
            parameters: vec![ParamDecl {
                name: "c".to_owned(),
                coeff_domain: CoeffDomain::Q,
                provenance: None,
            }],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::default(),
        },
        None,
    )
    .unwrap();
    assert!(matches!(
        execute_shigure_task(&task_bp, ShigureQueryKind::SemanticPreservation).verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet {
            ref condition,
            ..
        }) if condition == "before_presentation_must_be_parameter_free"
    ));
}

#[test]
fn rerun2_f1_z_unit_face_f2_nilpotent_reeval_f3_universal_ring_open() {
    // 1. F1 回帰: Z 上の InteractionAnalysis (UniversalRing) で非単元係数の切断面 `2*rho - 2 = 0`
    //    を `rho = 1` へ割らず沈黙する（F_2[delta,mu] では 2*0 - 2 = 0 でも残差が消えない）。
    let before_z = single_ledger_before(CoeffDomain::Z);
    let mut after_z = single_ledger_before(CoeffDomain::Z);
    after_z.name = "AfterZUnitFace".to_owned();
    after_z.operations[0].updates.insert(
        "x".to_owned(),
        PolyExpr::state("x")
            + PolyExpr::arg("u")
            + PolyExpr::param("mu")
                * PolyExpr::param("delta")
                * (PolyExpr::int(1) - PolyExpr::param("rho")),
    );
    let task_z_nonunit = CheckedShigureTask::validate(
        ComparisonPair {
            before: before_z,
            after: after_z,
            state_comparisons: vec![StateComparison {
                after_phase: "Active".to_owned(),
                before_phase: "Active".to_owned(),
                map: BTreeMap::from([("x".to_owned(), PolyExpr::state("x"))]),
                provenance: None,
            }],
            word_translation: WordTranslation {
                entries: vec![TranslatedWord {
                    after_operation: "apply".to_owned(),
                    steps: vec![TranslatedStep {
                        before_operation: "apply".to_owned(),
                        arg_exprs: vec![PolyExpr::arg("u")],
                    }],
                    provenance: None,
                }],
            },
        },
        ChangeSpec {
            name: "H_z_nonunit".to_owned(),
            coeff_domain: CoeffDomain::Z,
            parameters: vec![
                ParamDecl {
                    name: "mu".to_owned(),
                    coeff_domain: CoeffDomain::Z,
                    provenance: None,
                },
                ParamDecl {
                    name: "delta".to_owned(),
                    coeff_domain: CoeffDomain::Z,
                    provenance: None,
                },
                ParamDecl {
                    name: "rho".to_owned(),
                    coeff_domain: CoeffDomain::Z,
                    provenance: None,
                },
            ],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::default(),
        },
        Some(EvalCondition {
            name: "nonunit_face".to_owned(),
            evaluations: vec![],
            equations: vec![NamedPoly {
                name: "two_rho_eq_two".to_owned(),
                expr: PolyExpr::int(2) * PolyExpr::param("rho") - PolyExpr::int(2),
                provenance: None,
            }],
            invertibles: vec![],
            point_domain: PointDomain::UniversalRing,
            provenance: Provenance::default(),
        }),
    )
    .unwrap();
    let out_f1 = execute_shigure_task(&task_z_nonunit, ShigureQueryKind::InteractionAnalysis);
    assert!(matches!(
        out_f1.verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet {
            ref condition,
            ..
        }) if condition == "unit_integer_coordinate_face_required"
    ));

    // 2. F2 回帰: AlgebraicClosure 上の復元再評価で、`c*y = 0`, `x' = x + u + a^2`, `read = x + a*y`,
    //    `eval_condition: c = 0` の冪零差（`(a^2)` 対 `a`）を Nullstellensatz 幾何学的被覆で正しく受理する。
    let before_q = single_ledger_before(CoeffDomain::Q);
    let after_f2 = Presentation {
        name: "NilpotentReevalQ".to_owned(),
        coeff_domain: CoeffDomain::Q,
        sorts: vec![SortDecl {
            name: "D".to_owned(),
            rank: 1,
            coeff_domain: CoeffDomain::Q,
            provenance: None,
        }],
        phases: vec![PhaseDecl {
            name: "Active".to_owned(),
            coords: vec![CoordDecl::symbolic("x", "D"), CoordDecl::symbolic("y", "D")],
            state_laws: vec![StateLaw {
                name: "c_y_zero".to_owned(),
                kind: LawKind::Representation,
                polynomial: PolyExpr::param("c") * PolyExpr::state("y"),
                provenance: None,
            }],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "apply".to_owned(),
            source_phase: "Active".to_owned(),
            target_phase: "Active".to_owned(),
            args: vec![("u".to_owned(), "D".to_owned())],
            domain_laws: vec![],
            updates: BTreeMap::from([
                (
                    "x".to_owned(),
                    PolyExpr::state("x")
                        + PolyExpr::arg("u")
                        + PolyExpr::pow(PolyExpr::param("a"), 2),
                ),
                ("y".to_owned(), PolyExpr::state("y")),
            ]),
            provenance: None,
        }],
        observations: vec![ObservationDecl {
            name: "read".to_owned(),
            phase: "Active".to_owned(),
            components: vec![PolyExpr::state("x") + PolyExpr::param("a") * PolyExpr::state("y")],
            provenance: None,
        }],
        provenance: Provenance::default(),
    };
    let task_f2 = CheckedShigureTask::validate(
        ComparisonPair {
            before: before_q,
            after: after_f2,
            state_comparisons: vec![StateComparison {
                after_phase: "Active".to_owned(),
                before_phase: "Active".to_owned(),
                map: BTreeMap::from([("x".to_owned(), PolyExpr::state("x"))]),
                provenance: None,
            }],
            word_translation: WordTranslation {
                entries: vec![TranslatedWord {
                    after_operation: "apply".to_owned(),
                    steps: vec![TranslatedStep {
                        before_operation: "apply".to_owned(),
                        arg_exprs: vec![PolyExpr::arg("u")],
                    }],
                    provenance: None,
                }],
            },
        },
        ChangeSpec {
            name: "H_f2".to_owned(),
            coeff_domain: CoeffDomain::Q,
            parameters: vec![
                ParamDecl {
                    name: "a".to_owned(),
                    coeff_domain: CoeffDomain::Q,
                    provenance: None,
                },
                ParamDecl {
                    name: "c".to_owned(),
                    coeff_domain: CoeffDomain::Q,
                    provenance: None,
                },
            ],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::default(),
        },
        Some(EvalCondition {
            name: "c_zero".to_owned(),
            evaluations: vec![],
            equations: vec![NamedPoly {
                name: "c_eq_0".to_owned(),
                expr: PolyExpr::param("c"),
                provenance: None,
            }],
            invertibles: vec![],
            point_domain: PointDomain::AlgebraicClosure,
            provenance: Provenance::default(),
        }),
    )
    .unwrap();
    let out_f2 = execute_shigure_task(&task_f2, ShigureQueryKind::ConditionalSolutionSpace);
    assert_eq!(out_f2.verdict, Verdict::Established);
    let rest_f2 = out_f2.restored.expect("restored f2 artifact");
    assert!(rest_f2.reeval.checked && rest_f2.reeval.matched);
    assert_eq!(
        rest_f2.parameter_assignments.get("c").map(String::as_str),
        Some("0")
    );

    // 3. F3 回帰: UniversalRing + 開条件 D(a) と V(a) の組合せは、零環での成立と矛盾するため
    //    Refuted に落とさず事前ガードで `universal_ring_closed_equations_only` 沈黙を返す。
    let task_f3 = build_single_param_residual_task(
        CoeffDomain::Q,
        "a",
        PolyExpr::param("a"),
        Some(EvalCondition {
            name: "univ_open".to_owned(),
            evaluations: vec![],
            equations: vec![],
            invertibles: vec![NamedPoly {
                name: "a_inv".to_owned(),
                expr: PolyExpr::param("a"),
                provenance: None,
            }],
            point_domain: PointDomain::UniversalRing,
            provenance: Provenance::default(),
        }),
    );
    let out_f3 = execute_shigure_task(&task_f3, ShigureQueryKind::ConditionalSolutionSpace);
    assert!(matches!(
        out_f3.verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet {
            ref condition,
            ..
        }) if condition == "universal_ring_closed_equations_only"
    ));
}
