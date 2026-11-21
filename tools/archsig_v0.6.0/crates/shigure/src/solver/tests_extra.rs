use super::*;
use crate::ir::change::{
    ChangeSpec, EditableTarget, EvalCondition, NamedPoly, ParamDecl, PointDomain,
};
use crate::ir::presentation::{
    ComparisonPair, CoordDecl, LawKind, ObservationDecl, OperationDecl, PhaseDecl, Presentation,
    SortDecl, StateComparison, StateLaw, TranslatedStep, TranslatedWord, WordTranslation,
};
use crate::ir::provenance::Provenance;
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::ir::validate::CheckedShigureTask;
use crate::solver::tests::{
    build_ledger_snapshot_task, build_single_param_residual_task, q_lit, single_ledger_before,
};
use num_bigint::{BigInt, BigUint};
use std::collections::BTreeMap;

#[test]
fn ac4_interaction_analysis_distinguishes_mu_delta_t_pow_m_faces_and_open_silence() {
    // 1. 台帳 mu*delta: 2 変数相互作用、極小不成立部分族 {delta, mu}、r = 1。
    let out_p3 = execute_shigure_task(
        &build_ledger_snapshot_task(false, true, None),
        ShigureQueryKind::InteractionAnalysis,
    );
    assert_eq!(out_p3.verdict, Verdict::Established);
    let s2 = out_p3.interaction.expect("interaction summary");
    assert_eq!(s2.min_interacting_variables, Some(2));
    assert_eq!(s2.max_vanishing_subset_size, Some(1));
    assert_eq!(
        s2.minimal_failing_subsets,
        vec![vec!["delta".to_owned(), "mu".to_owned()]]
    );

    // 2. 単変数高次 t^m (m = 1, 2, 3, 5): 常に 1 変数相互作用、r = 0。
    for m in [1u32, 2, 3, 5] {
        let task_tm = build_single_param_residual_task(
            CoeffDomain::Q,
            "t",
            PolyExpr::pow(PolyExpr::param("t"), m),
            None,
        );
        let out_tm = execute_shigure_task(&task_tm, ShigureQueryKind::InteractionAnalysis);
        assert_eq!(out_tm.verdict, Verdict::Established);
        let st = out_tm.interaction.expect("t^m interaction summary");
        assert_eq!(st.min_interacting_variables, Some(1));
        assert_eq!(st.max_vanishing_subset_size, Some(0));
        assert_eq!(st.minimal_failing_subsets, vec![vec!["t".to_owned()]]);
    }

    // 3. 3 変数 mu*delta*(1 - rho): rho = 0 面は {delta, mu} 不成立、rho = 1 面は解消。
    let face_rho0_cond = EvalCondition {
        name: "face_rho_0".to_owned(),
        evaluations: vec![],
        equations: vec![NamedPoly::new("rho_0", PolyExpr::param("rho"))],
        invertibles: vec![],
        point_domain: PointDomain::UniversalRing,
        provenance: Provenance::default(),
    };
    let out_rho0 = execute_shigure_task(
        &build_ledger_snapshot_task(true, false, Some(face_rho0_cond)),
        ShigureQueryKind::InteractionAnalysis,
    );
    assert_eq!(out_rho0.verdict, Verdict::Established);
    let s_rho0 = out_rho0.interaction.expect("rho=0 interaction");
    assert_eq!(s_rho0.min_interacting_variables, Some(2));
    assert_eq!(s_rho0.max_vanishing_subset_size, Some(1));
    assert_eq!(
        s_rho0.minimal_failing_subsets,
        vec![vec!["delta".to_owned(), "mu".to_owned()]]
    );

    let face_rho1_cond = EvalCondition {
        name: "face_rho_1".to_owned(),
        evaluations: vec![],
        equations: vec![NamedPoly::new("rho_1", PolyExpr::param("rho") - q_lit(1))],
        invertibles: vec![],
        point_domain: PointDomain::UniversalRing,
        provenance: Provenance::default(),
    };
    let out_rho1 = execute_shigure_task(
        &build_ledger_snapshot_task(true, false, Some(face_rho1_cond)),
        ShigureQueryKind::InteractionAnalysis,
    );
    assert_eq!(out_rho1.verdict, Verdict::Established);
    let s_rho1 = out_rho1.interaction.expect("rho=1 interaction");
    assert_eq!(s_rho1.min_interacting_variables, None);
    assert_eq!(s_rho1.max_vanishing_subset_size, Some(2));
    assert!(s_rho1.minimal_failing_subsets.is_empty());

    // 4. 明示開条件 D(mu) や非座標面制約（delta - mu = 0）は閉条件へ丸めず沈黙。
    let open_cond = EvalCondition {
        name: "open_for_interaction".to_owned(),
        evaluations: vec![],
        equations: vec![],
        invertibles: vec![NamedPoly::new("mu_unit", PolyExpr::param("mu"))],
        point_domain: PointDomain::AlgebraicClosure,
        provenance: Provenance::default(),
    };
    let out_open = execute_shigure_task(
        &build_ledger_snapshot_task(false, true, Some(open_cond)),
        ShigureQueryKind::InteractionAnalysis,
    );
    assert!(matches!(
        out_open.verdict,
        Verdict::Undetermined(SilenceReason::OpenConditionInInteraction { .. })
    ));

    let non_coord_cond = EvalCondition {
        name: "non_coord_slice".to_owned(),
        evaluations: vec![],
        equations: vec![NamedPoly::new(
            "diag",
            PolyExpr::param("delta") - PolyExpr::param("mu"),
        )],
        invertibles: vec![],
        point_domain: PointDomain::UniversalRing,
        provenance: Provenance::default(),
    };
    let out_nc = execute_shigure_task(
        &build_ledger_snapshot_task(false, true, Some(non_coord_cond)),
        ShigureQueryKind::InteractionAnalysis,
    );
    assert!(matches!(
        out_nc.verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet {
            ref condition,
            ..
        }) if condition == "free_parameter_chart_required"
    ));

    // 5. 商環ローカス自体が開集合 D(a) のみ（R[y]/(a*y) で y = 0）の場合も閉条件へ丸めず沈黙。
    let before = single_ledger_before(CoeffDomain::Q);
    let after_open_quot = Presentation {
        name: "OpenQuotAfter".to_owned(),
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
    let pair_oq = ComparisonPair {
        before,
        after: after_open_quot,
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
    };
    let cs_oq = ChangeSpec {
        name: "H_oq".to_owned(),
        coeff_domain: CoeffDomain::Q,
        parameters: vec![ParamDecl {
            name: "a".to_owned(),
            coeff_domain: CoeffDomain::Q,
            provenance: None,
        }],
        fixed: vec![],
        editable: vec![],
        provenance: Provenance::default(),
    };
    let task_oq = CheckedShigureTask::validate(pair_oq, cs_oq, None).unwrap();
    let out_oq = execute_shigure_task(&task_oq, ShigureQueryKind::InteractionAnalysis);
    assert!(matches!(
        out_oq.verdict,
        Verdict::Undetermined(SilenceReason::OpenConditionInInteraction { .. })
    ));
}

#[test]
fn ac5_b_silence_discipline_domains_unobserved_rank_and_fp_restoration() {
    // 1. x^2 + 1 = 0: AlgebraicClosure では Established、Q_points / Z_points では沈黙。
    let x2_p1_q = PolyExpr::pow(PolyExpr::param("k"), 2) + q_lit(1);
    let cond_closure = EvalCondition {
        name: "closure".to_owned(),
        evaluations: vec![],
        equations: vec![],
        invertibles: vec![],
        point_domain: PointDomain::AlgebraicClosure,
        provenance: Provenance::default(),
    };
    let out_cl = execute_shigure_task(
        &build_single_param_residual_task(CoeffDomain::Q, "k", x2_p1_q.clone(), Some(cond_closure)),
        ShigureQueryKind::ConditionalSolutionSpace,
    );
    assert_eq!(out_cl.verdict, Verdict::Established);

    let cond_q = EvalCondition {
        name: "q_pts".to_owned(),
        evaluations: vec![],
        equations: vec![],
        invertibles: vec![],
        point_domain: PointDomain::RationalPoints,
        provenance: Provenance::default(),
    };
    let out_q = execute_shigure_task(
        &build_single_param_residual_task(CoeffDomain::Q, "k", x2_p1_q, Some(cond_q)),
        ShigureQueryKind::ConditionalSolutionSpace,
    );
    assert!(matches!(
        out_q.verdict,
        Verdict::Undetermined(SilenceReason::NonLinearRationalOrIntegerExistence {
            point_domain: PointDomain::RationalPoints,
            ..
        })
    ));

    let x2_p1_z = PolyExpr::pow(PolyExpr::param("k"), 2) + PolyExpr::int(1);
    let cond_z = EvalCondition {
        name: "z_pts".to_owned(),
        evaluations: vec![],
        equations: vec![],
        invertibles: vec![],
        point_domain: PointDomain::IntegerPoints,
        provenance: Provenance::default(),
    };
    let out_z = execute_shigure_task(
        &build_single_param_residual_task(CoeffDomain::Z, "k", x2_p1_z, Some(cond_z)),
        ShigureQueryKind::ConditionalSolutionSpace,
    );
    assert!(matches!(
        out_z.verdict,
        Verdict::Undetermined(SilenceReason::NonLinearRationalOrIntegerExistence {
            point_domain: PointDomain::IntegerPoints,
            ..
        })
    ));

    // 2. Z 上アフィン 2*k - 3 = 0: Z_points では Refuted（Smith 標準形）、Q_points では Established（k = 3/2）。
    let aff_z = PolyExpr::int(2) * PolyExpr::param("k") - PolyExpr::int(3);
    let out_aff_z = execute_shigure_task(
        &build_single_param_residual_task(
            CoeffDomain::Z,
            "k",
            aff_z,
            Some(EvalCondition {
                name: "z_aff".to_owned(),
                evaluations: vec![],
                equations: vec![],
                invertibles: vec![],
                point_domain: PointDomain::IntegerPoints,
                provenance: Provenance::default(),
            }),
        ),
        ShigureQueryKind::ConditionalSolutionSpace,
    );
    assert_eq!(out_aff_z.verdict, Verdict::Refuted);

    let aff_q = q_lit(2) * PolyExpr::param("k") - q_lit(3);
    let out_aff_q = execute_shigure_task(
        &build_single_param_residual_task(
            CoeffDomain::Q,
            "k",
            aff_q,
            Some(EvalCondition {
                name: "q_aff".to_owned(),
                evaluations: vec![],
                equations: vec![],
                invertibles: vec![],
                point_domain: PointDomain::RationalPoints,
                provenance: Provenance::default(),
            }),
        ),
        ShigureQueryKind::ConditionalSolutionSpace,
    );
    assert_eq!(out_aff_q.verdict, Verdict::Established);
    let rest_q = out_aff_q.restored.expect("restored Q affine");
    assert_eq!(rest_q.parameter_assignments["k"], "3/2");
    assert!(rest_q.reeval.checked && rest_q.reeval.matched);

    // 3. F_5 上の有限全列挙と復元・再評価一致: k^2 + 1 = 0 in F_5 has solutions k = 2, 3.
    let p5 = BigUint::from(5u32);
    let one_fp5 = PolyExpr::Const(ScalarLit::fp(BigInt::from(1), p5.clone()).unwrap());
    let x2_p1_fp5 = PolyExpr::pow(PolyExpr::param("k"), 2) + one_fp5;
    let out_fp5 = execute_shigure_task(
        &build_single_param_residual_task(
            CoeffDomain::Fp(p5.clone()),
            "k",
            x2_p1_fp5,
            Some(EvalCondition {
                name: "fp5_pts".to_owned(),
                evaluations: vec![],
                equations: vec![],
                invertibles: vec![],
                point_domain: PointDomain::FiniteFieldPoints(p5),
                provenance: Provenance::default(),
            }),
        ),
        ShigureQueryKind::ConditionalSolutionSpace,
    );
    assert_eq!(out_fp5.verdict, Verdict::Established);
    let rest_fp5 = out_fp5.restored.expect("restored F_5 solution");
    assert_eq!(rest_fp5.parameter_assignments["k"], "2");
    assert!(rest_fp5.reeval.checked && rest_fp5.reeval.matched);

    // 4. 未観測欠測（PolyExpr::Unobserved および CoordValue::Missing）は零化せず沈黙。
    let task_unobs = build_single_param_residual_task(
        CoeffDomain::Q,
        "k",
        PolyExpr::unobserved("ParamAfter.Active.missing_delta", None),
        None,
    );
    let out_unobs = execute_shigure_task(&task_unobs, ShigureQueryKind::SemanticPreservation);
    assert_eq!(
        out_unobs.verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency {
            slots: vec!["ParamAfter.Active.missing_delta".to_owned()],
        })
    );

    let before_m = single_ledger_before(CoeffDomain::Q);
    let mut after_m = single_ledger_before(CoeffDomain::Q);
    after_m.name = "AfterMissingCoord".to_owned();
    after_m.phases[0].coords[0] = CoordDecl::missing("x", "D");
    let task_m = CheckedShigureTask::validate(
        ComparisonPair {
            before: before_m,
            after: after_m,
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
            name: "H_missing".to_owned(),
            coeff_domain: CoeffDomain::Q,
            parameters: vec![],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::default(),
        },
        None,
    )
    .unwrap();
    let out_m = execute_shigure_task(&task_m, ShigureQueryKind::SemanticPreservation);
    assert_eq!(
        out_m.verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency {
            slots: vec!["AfterMissingCoord.Active.x".to_owned()],
        })
    );

    // 5. sort rank > 1 および EditableTarget(before) は fail-closed で沈黙。
    let mut before_r2 = single_ledger_before(CoeffDomain::Q);
    before_r2.sorts[0].rank = 2;
    let mut after_r2 = single_ledger_before(CoeffDomain::Q);
    after_r2.name = "AfterR2".to_owned();
    after_r2.sorts[0].rank = 2;
    let task_r2 = CheckedShigureTask::validate(
        ComparisonPair {
            before: before_r2,
            after: after_r2,
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
            name: "H_r2".to_owned(),
            coeff_domain: CoeffDomain::Q,
            parameters: vec![],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::default(),
        },
        None,
    )
    .unwrap();
    let out_r2 = execute_shigure_task(&task_r2, ShigureQueryKind::SemanticPreservation);
    assert!(matches!(
        out_r2.verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet {
            ref condition,
            ..
        }) if condition == "sort_rank_one_required"
    ));

    let before_ed = single_ledger_before(CoeffDomain::Q);
    let mut after_ed = single_ledger_before(CoeffDomain::Q);
    after_ed.name = "AfterEd".to_owned();
    let task_ed = CheckedShigureTask::validate(
        ComparisonPair {
            before: before_ed,
            after: after_ed,
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
            name: "H_ed_before".to_owned(),
            coeff_domain: CoeffDomain::Q,
            parameters: vec![],
            fixed: vec![],
            editable: vec![EditableTarget::OperationExpr {
                presentation: "SingleLedger".to_owned(),
                operation: "apply".to_owned(),
            }],
            provenance: Provenance::default(),
        },
        None,
    )
    .unwrap();
    let out_ed = execute_shigure_task(&task_ed, ShigureQueryKind::ConditionalSolutionSpace);
    assert!(matches!(
        out_ed.verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet {
            ref condition,
            ..
        }) if condition == "editable_target_must_be_after"
    ));
}

#[test]
fn z_points_open_witness_and_refutation_and_non_integer_face_guard() {
    // 1. Z_points: k = 0 かつ D(k) => Refuted + verified EmptyWitness（Undetermined にならない）。
    let out_z_empty = execute_shigure_task(
        &build_single_param_residual_task(
            CoeffDomain::Z,
            "k",
            PolyExpr::param("k"),
            Some(EvalCondition {
                name: "z_empty_open".to_owned(),
                evaluations: vec![],
                equations: vec![],
                invertibles: vec![NamedPoly::new("k_unit", PolyExpr::param("k"))],
                point_domain: PointDomain::IntegerPoints,
                provenance: Provenance::default(),
            }),
        ),
        ShigureQueryKind::ConditionalSolutionSpace,
    );
    assert_eq!(out_z_empty.verdict, Verdict::Refuted);
    assert!(out_z_empty.empty_witness.expect("empty witness").verified);

    // 2. Z_points: 2*k - 2 = 0 かつ D(k) => k = 1 ∈ Z^× なので Established（復元・再評価一致）。
    let out_z_ok = execute_shigure_task(
        &build_single_param_residual_task(
            CoeffDomain::Z,
            "k",
            PolyExpr::int(2) * PolyExpr::param("k") - PolyExpr::int(2),
            Some(EvalCondition {
                name: "z_ok_unit".to_owned(),
                evaluations: vec![],
                equations: vec![],
                invertibles: vec![NamedPoly::new("k_unit", PolyExpr::param("k"))],
                point_domain: PointDomain::IntegerPoints,
                provenance: Provenance::default(),
            }),
        ),
        ShigureQueryKind::ConditionalSolutionSpace,
    );
    assert_eq!(out_z_ok.verdict, Verdict::Established);
    let rest = out_z_ok.restored.expect("restored Z unit solution");
    assert_eq!(rest.parameter_assignments["k"], "1");
    assert!(rest.reeval.checked && rest.reeval.matched);

    // 2b. Z_points: 2*k - 4 = 0 かつ D(k) => k = 2 ∉ Z^×（Z で単元でない）なので Refuted（F3 回帰）。
    let out_z_non_unit = execute_shigure_task(
        &build_single_param_residual_task(
            CoeffDomain::Z,
            "k",
            PolyExpr::int(2) * PolyExpr::param("k") - PolyExpr::int(4),
            Some(EvalCondition {
                name: "z_non_unit".to_owned(),
                evaluations: vec![],
                equations: vec![],
                invertibles: vec![NamedPoly::new("k_unit", PolyExpr::param("k"))],
                point_domain: PointDomain::IntegerPoints,
                provenance: Provenance::default(),
            }),
        ),
        ShigureQueryKind::ConditionalSolutionSpace,
    );
    assert_eq!(out_z_non_unit.verdict, Verdict::Refuted);

    // 3. Z 上の InteractionAnalysis で非整数切断面 2*k - 1 = 0 は fail-closed で拒否される。
    let out_z_face = execute_shigure_task(
        &build_single_param_residual_task(
            CoeffDomain::Z,
            "k",
            PolyExpr::pow(PolyExpr::param("k"), 2),
            Some(EvalCondition {
                name: "half_face".to_owned(),
                evaluations: vec![],
                equations: vec![NamedPoly::new(
                    "two_k_minus_1",
                    PolyExpr::int(2) * PolyExpr::param("k") - PolyExpr::int(1),
                )],
                invertibles: vec![],
                point_domain: PointDomain::UniversalRing,
                provenance: Provenance::default(),
            }),
        ),
        ShigureQueryKind::InteractionAnalysis,
    );
    assert!(matches!(
        out_z_face.verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet {
            ref condition,
            ..
        }) if condition == "integer_coordinate_face_required"
    ));
}

#[test]
fn review_regressions_multistratum_z_torsion_universal_ring_and_multistep_translation() {
    // F1 回帰: Q_points で 2 層の非閉ローカス（strata[0] が非線形 V(k^2+1, a)、
    // strata[1] が有理点を持つ V(a-1) ∩ D(k^2+1)）に対し、先頭層で誤って Undetermined にならず Established を返す。
    let before_q = single_ledger_before(CoeffDomain::Q);
    let k2_plus_1 = PolyExpr::pow(PolyExpr::param("k"), 2) + q_lit(1);
    let after_f1 = Presentation {
        name: "MultiStratumQ".to_owned(),
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
                name: "k2p1_y".to_owned(),
                kind: LawKind::Representation,
                polynomial: k2_plus_1.clone() * PolyExpr::state("y"),
                provenance: None,
            }],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "apply".to_owned(),
            source_phase: "Active".to_owned(),
            target_phase: "Active".to_owned(),
            args: vec![("u".to_owned(), "D".to_owned())],
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
                    + PolyExpr::param("a") * PolyExpr::state("y")
                    + k2_plus_1 * (PolyExpr::param("a") - q_lit(1)),
            ],
            provenance: None,
        }],
        provenance: Provenance::default(),
    };
    let task_f1 = CheckedShigureTask::validate(
        ComparisonPair {
            before: before_q,
            after: after_f1,
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
            name: "H_f1".to_owned(),
            coeff_domain: CoeffDomain::Q,
            parameters: vec![
                ParamDecl {
                    name: "a".to_owned(),
                    coeff_domain: CoeffDomain::Q,
                    provenance: None,
                },
                ParamDecl {
                    name: "k".to_owned(),
                    coeff_domain: CoeffDomain::Q,
                    provenance: None,
                },
            ],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::default(),
        },
        Some(EvalCondition {
            name: "f1_q_points".to_owned(),
            evaluations: vec![],
            equations: vec![],
            invertibles: vec![],
            point_domain: PointDomain::RationalPoints,
            provenance: Provenance::default(),
        }),
    )
    .unwrap();
    let out_f1 = execute_shigure_task(&task_f1, ShigureQueryKind::ConditionalSolutionSpace);
    assert_eq!(out_f1.verdict, Verdict::Established);
    let rest_f1 = out_f1.restored.expect("stratum 1 must be restored");
    assert_eq!(rest_f1.parameter_assignments["a"], "1");
    assert!(rest_f1.parameter_assignments.contains_key("k"));
    assert!(rest_f1.free_parameters.is_empty());
    assert!(rest_f1.reeval.checked && rest_f1.reeval.matched);

    // F2 回帰: CoeffDomain::Z で Z-捩れを持つ状態 Law `2*y = 0`（read = x + y）は
    // Q 商環へフォールバックせず IntegerPoints / InteractionAnalysis ともに QuotientIdealOutOfScope で沈黙。
    let before_z = single_ledger_before(CoeffDomain::Z);
    let after_z_torsion = Presentation {
        name: "ZTorsion".to_owned(),
        coeff_domain: CoeffDomain::Z,
        sorts: vec![SortDecl {
            name: "D".to_owned(),
            rank: 1,
            coeff_domain: CoeffDomain::Z,
            provenance: None,
        }],
        phases: vec![PhaseDecl {
            name: "Active".to_owned(),
            coords: vec![CoordDecl::symbolic("x", "D"), CoordDecl::symbolic("y", "D")],
            state_laws: vec![StateLaw {
                name: "two_y_zero".to_owned(),
                kind: LawKind::Representation,
                polynomial: PolyExpr::int(2) * PolyExpr::state("y"),
                provenance: None,
            }],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "apply".to_owned(),
            source_phase: "Active".to_owned(),
            target_phase: "Active".to_owned(),
            args: vec![("u".to_owned(), "D".to_owned())],
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
    let pair_f2 = ComparisonPair {
        before: before_z,
        after: after_z_torsion,
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
    };
    let cs_f2 = ChangeSpec {
        name: "H_f2".to_owned(),
        coeff_domain: CoeffDomain::Z,
        parameters: vec![],
        fixed: vec![],
        editable: vec![],
        provenance: Provenance::default(),
    };
    let task_f2 = CheckedShigureTask::validate(
        pair_f2.clone(),
        cs_f2.clone(),
        Some(EvalCondition {
            name: "f2_z_points".to_owned(),
            evaluations: vec![],
            equations: vec![],
            invertibles: vec![],
            point_domain: PointDomain::IntegerPoints,
            provenance: Provenance::default(),
        }),
    )
    .unwrap();
    assert!(matches!(
        execute_shigure_task(&task_f2, ShigureQueryKind::ConditionalSolutionSpace).verdict,
        Verdict::Undetermined(SilenceReason::QuotientIdealOutOfScope { .. })
    ));
    let task_f2_univ = CheckedShigureTask::validate(pair_f2, cs_f2, None).unwrap();
    assert!(matches!(
        execute_shigure_task(&task_f2_univ, ShigureQueryKind::SemanticPreservation).verdict,
        Verdict::Undetermined(SilenceReason::QuotientIdealOutOfScope { .. })
    ));
    assert!(matches!(
        execute_shigure_task(&task_f2_univ, ShigureQueryKind::InteractionAnalysis).verdict,
        Verdict::Undetermined(SilenceReason::QuotientIdealOutOfScope { .. })
    ));

    // F4 回帰: UniversalRing での (Fp(3), k^2+1=0) と (Z, 2k-1=0) は誤反証・非整数復元せず沈黙。
    let p3 = BigUint::from(3u32);
    let one_fp3 = PolyExpr::Const(ScalarLit::fp(BigInt::from(1), p3.clone()).unwrap());
    let out_f4_fp = execute_shigure_task(
        &build_single_param_residual_task(
            CoeffDomain::Fp(p3),
            "k",
            PolyExpr::pow(PolyExpr::param("k"), 2) + one_fp3,
            Some(EvalCondition {
                name: "f4_fp_univ".to_owned(),
                evaluations: vec![],
                equations: vec![],
                invertibles: vec![],
                point_domain: PointDomain::UniversalRing,
                provenance: Provenance::default(),
            }),
        ),
        ShigureQueryKind::ConditionalSolutionSpace,
    );
    assert!(matches!(
        out_f4_fp.verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { .. })
    ));

    let out_f4_z = execute_shigure_task(
        &build_single_param_residual_task(
            CoeffDomain::Z,
            "k",
            PolyExpr::int(2) * PolyExpr::param("k") - PolyExpr::int(1),
            Some(EvalCondition {
                name: "f4_z_univ".to_owned(),
                evaluations: vec![],
                equations: vec![],
                invertibles: vec![],
                point_domain: PointDomain::UniversalRing,
                provenance: Provenance::default(),
            }),
        ),
        ShigureQueryKind::ConditionalSolutionSpace,
    );
    assert!(matches!(
        out_f4_z.verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { .. })
    ));

    // 追加カバレッジ: 2 ステップ語翻訳（apply_twice -> [apply(u), apply(u)]）+ Observed 座標。
    let before_2s = single_ledger_before(CoeffDomain::Q);
    let after_2s = Presentation {
        name: "TwiceAfter".to_owned(),
        coeff_domain: CoeffDomain::Q,
        sorts: vec![SortDecl {
            name: "D".to_owned(),
            rank: 1,
            coeff_domain: CoeffDomain::Q,
            provenance: None,
        }],
        phases: vec![PhaseDecl {
            name: "Active".to_owned(),
            coords: vec![
                CoordDecl::symbolic("x", "D"),
                CoordDecl::observed("bias", "D", ScalarLit::rat(0, 1).unwrap()),
            ],
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "apply_twice".to_owned(),
            source_phase: "Active".to_owned(),
            target_phase: "Active".to_owned(),
            args: vec![("u".to_owned(), "D".to_owned())],
            updates: BTreeMap::from([
                (
                    "x".to_owned(),
                    PolyExpr::state("x")
                        + PolyExpr::param("c") * PolyExpr::arg("u")
                        + PolyExpr::state("bias"),
                ),
                ("bias".to_owned(), PolyExpr::state("bias")),
            ]),
            provenance: None,
        }],
        observations: vec![ObservationDecl {
            name: "read".to_owned(),
            phase: "Active".to_owned(),
            components: vec![PolyExpr::state("x") + PolyExpr::state("bias")],
            provenance: None,
        }],
        provenance: Provenance::default(),
    };
    let task_2s = CheckedShigureTask::validate(
        ComparisonPair {
            before: before_2s,
            after: after_2s,
            state_comparisons: vec![StateComparison {
                after_phase: "Active".to_owned(),
                before_phase: "Active".to_owned(),
                map: BTreeMap::from([("x".to_owned(), PolyExpr::state("x"))]),
                provenance: None,
            }],
            word_translation: WordTranslation {
                entries: vec![TranslatedWord {
                    after_operation: "apply_twice".to_owned(),
                    steps: vec![
                        TranslatedStep {
                            before_operation: "apply".to_owned(),
                            arg_exprs: vec![PolyExpr::arg("u")],
                        },
                        TranslatedStep {
                            before_operation: "apply".to_owned(),
                            arg_exprs: vec![PolyExpr::arg("u")],
                        },
                    ],
                    provenance: None,
                }],
            },
        },
        ChangeSpec {
            name: "H_2step".to_owned(),
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
    let out_2s = execute_shigure_task(&task_2s, ShigureQueryKind::ConditionalSolutionSpace);
    assert_eq!(out_2s.verdict, Verdict::Established);
    let rest_2s = out_2s.restored.expect("restored 2-step translation");
    assert_eq!(rest_2s.parameter_assignments["c"], "2");
    assert_eq!(
        rest_2s.word_translation["apply_twice"],
        vec!["apply(u)".to_owned(), "apply(u)".to_owned()]
    );
    assert!(rest_2s.reeval.checked && rest_2s.reeval.matched);
}
