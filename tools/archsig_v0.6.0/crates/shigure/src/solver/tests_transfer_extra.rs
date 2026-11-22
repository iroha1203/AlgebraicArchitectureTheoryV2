use super::tests_transfer::{clit, empty_cs, orig, pair_bc};
use crate::ir::change::{EvalCondition, NamedPoly, PointDomain};
use crate::ir::presentation::{
    ComparisonPair, CoordDecl, LawKind, ObservationDecl, PhaseDecl, Presentation, SortDecl,
    StateComparison, StateLaw, WordTranslation,
};
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::result_ext::DomainRelation;
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::ir::transfer::{
    CheckedTransferTask, OldWordLiftSpec, TransferSpec, TransferStepSpec, WordCheckSpec,
    WordStepExpr,
};
use crate::solver::solve_transfer_task;
use std::collections::BTreeMap;

fn id_single_pres(name: &str, domain: CoeffDomain, laws: Vec<StateLaw>) -> Presentation {
    Presentation {
        name: name.into(),
        coeff_domain: domain.clone(),
        sorts: vec![SortDecl {
            name: "D".into(),
            rank: 1,
            coeff_domain: domain,
            provenance: Some(orig("d")),
        }],
        phases: vec![PhaseDecl {
            name: "S".into(),
            coords: vec![CoordDecl::symbolic("x", "D")],
            state_laws: laws,
            provenance: None,
        }],
        operations: vec![],
        observations: vec![ObservationDecl {
            name: "read".into(),
            phase: "S".into(),
            components: vec![PolyExpr::state("x")],
            provenance: None,
        }],
        provenance: Provenance::new(vec![orig(name)], vec![MathClause::G140G3]),
    }
}

#[test]
fn transfer_m01_nonlinear_rational_and_integer_silence() {
    let q = CoeffDomain::Q;
    let mut cmp_q_fixed = pair_bc("X0", "X1", q.clone(), true);
    cmp_q_fixed.before.phases[0].coords = vec![CoordDecl::symbolic("x", "D")];
    cmp_q_fixed.after.phases[0].coords =
        vec![CoordDecl::symbolic("b", "D"), CoordDecl::symbolic("c", "D")];
    cmp_q_fixed.after.operations[0].domain_laws = vec![StateLaw {
        name: "b2p1".into(),
        kind: LawKind::Semantic,
        polynomial: PolyExpr::pow(PolyExpr::state("b"), 2) + clit(&q, 1),
        provenance: None,
    }];
    cmp_q_fixed.before.operations[0].domain_laws = vec![StateLaw {
        name: "x2p1".into(),
        kind: LawKind::Semantic,
        polynomial: PolyExpr::pow(PolyExpr::state("x"), 2) + clit(&q, 1),
        provenance: None,
    }];
    cmp_q_fixed.after.observations[0].components = vec![PolyExpr::state("b")];
    cmp_q_fixed.state_comparisons[0].map = BTreeMap::from([("x".into(), PolyExpr::state("b"))]);

    let spec_q_rat = TransferSpec {
        name: "m01_q_rat_dw".into(),
        steps: vec![TransferStepSpec {
            name: "s0".into(),
            comparison: cmp_q_fixed,
            source_phase: "Idle".into(),
            domain_laws: vec![],
            target_phase: "Idle".into(),
            lift_map: BTreeMap::from([
                ("b".into(), PolyExpr::state("x")),
                ("c".into(), clit(&q, 0)),
            ]),
            provenance: None,
        }],
        word_checks: vec![WordCheckSpec {
            name: "w_nl".into(),
            args: vec!["v".into()],
            steps: vec![WordStepExpr {
                operation: "apply".into(),
                arg_exprs: vec![PolyExpr::arg("v")],
            }],
            provenance: None,
        }],
        old_word_lifts: vec![],
        change_spec: empty_cs(q, vec![]),
        eval_condition: Some(EvalCondition {
            name: "ratpts".into(),
            evaluations: vec![],
            equations: vec![],
            invertibles: vec![],
            point_domain: PointDomain::RationalPoints,
            provenance: Provenance::new(vec![orig("ratpts")], vec![MathClause::G141D4]),
        }),
        require_full_domain: false,
        provenance: Provenance::new(vec![orig("m01q")], vec![MathClause::G140G2]),
    };
    assert!(matches!(
        solve_transfer_task(&CheckedTransferTask::validate(spec_q_rat).unwrap()).verdict,
        Verdict::Undetermined(SilenceReason::NonLinearRationalOrIntegerExistence {
            point_domain: PointDomain::RationalPoints,
            ..
        })
    ));

    let z = CoeffDomain::Z;
    let z0 = id_single_pres("Z0", z.clone(), vec![]);
    let z1 = id_single_pres("Z1", z.clone(), vec![]);
    let z2 = id_single_pres("Z2", z.clone(), vec![]);
    let z_cmp = |a: &Presentation, b: &Presentation| ComparisonPair {
        before: a.clone(),
        after: b.clone(),
        state_comparisons: vec![StateComparison {
            after_phase: "S".into(),
            before_phase: "S".into(),
            map: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
            provenance: None,
        }],
        word_translation: WordTranslation { entries: vec![] },
    };
    let spec_z_int = TransferSpec {
        name: "m01_z_int_d0k".into(),
        steps: vec![
            TransferStepSpec {
                name: "s1".into(),
                comparison: z_cmp(&z0, &z1),
                source_phase: "S".into(),
                domain_laws: vec![],
                target_phase: "S".into(),
                lift_map: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
                provenance: None,
            },
            TransferStepSpec {
                name: "s2".into(),
                comparison: z_cmp(&z1, &z2),
                source_phase: "S".into(),
                domain_laws: vec![StateLaw {
                    name: "x2m2".into(),
                    kind: LawKind::Semantic,
                    polynomial: PolyExpr::pow(PolyExpr::state("x"), 2) - clit(&z, 2),
                    provenance: None,
                }],
                target_phase: "S".into(),
                lift_map: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
                provenance: None,
            },
        ],
        word_checks: vec![],
        old_word_lifts: vec![],
        change_spec: empty_cs(z, vec![]),
        eval_condition: Some(EvalCondition {
            name: "intpts".into(),
            evaluations: vec![],
            equations: vec![],
            invertibles: vec![],
            point_domain: PointDomain::IntegerPoints,
            provenance: Provenance::new(vec![orig("intpts")], vec![MathClause::G141D4]),
        }),
        require_full_domain: false,
        provenance: Provenance::new(vec![orig("m01z")], vec![MathClause::G140G3]),
    };
    assert!(matches!(
        solve_transfer_task(&CheckedTransferTask::validate(spec_z_int).unwrap()).verdict,
        Verdict::Undetermined(SilenceReason::NonLinearRationalOrIntegerExistence {
            point_domain: PointDomain::IntegerPoints,
            ..
        })
    ));
}

#[test]
fn transfer_m05_lifts_nonlinear_and_word_eval_invertibles() {
    let q = CoeffDomain::Q;
    let cmp_deg2 = pair_bc("X0", "X1", q.clone(), true);
    let out_deg2 = solve_transfer_task(
        &CheckedTransferTask::validate(TransferSpec {
            name: "m05_deg2_lift".into(),
            steps: vec![TransferStepSpec {
                name: "s".into(),
                comparison: cmp_deg2,
                source_phase: "Idle".into(),
                domain_laws: vec![],
                target_phase: "Idle".into(),
                lift_map: BTreeMap::from([
                    ("b".into(), PolyExpr::state("x")),
                    ("c".into(), clit(&q, 0)),
                ]),
                provenance: None,
            }],
            word_checks: vec![],
            old_word_lifts: vec![OldWordLiftSpec {
                name: "lift_sq".into(),
                args: vec!["v".into()],
                target_steps: vec![WordStepExpr {
                    operation: "apply".into(),
                    arg_exprs: vec![PolyExpr::pow(PolyExpr::arg("v"), 2)],
                }],
                max_length: Some(1),
                provenance: None,
            }],
            change_spec: empty_cs(q.clone(), vec![]),
            eval_condition: None,
            require_full_domain: false,
            provenance: Provenance::new(vec![orig("m05a")], vec![MathClause::G140G2]),
        })
        .unwrap(),
    );
    assert_eq!(out_deg2.verdict, Verdict::Established);
    assert!(out_deg2.transfer.unwrap().old_word_lifts[0].lift_found);

    let mut cmp_zero_arg = pair_bc("X0", "X1", q.clone(), true);
    cmp_zero_arg.after.operations[0].domain_laws = vec![StateLaw {
        name: "u2m1".into(),
        kind: LawKind::Semantic,
        polynomial: PolyExpr::pow(PolyExpr::arg("u"), 2) - clit(&q, 1),
        provenance: None,
    }];
    cmp_zero_arg.after.operations[0].updates = BTreeMap::from([
        ("b".into(), PolyExpr::state("b")),
        ("c".into(), PolyExpr::state("c")),
    ]);
    cmp_zero_arg.before.operations[0].updates =
        BTreeMap::from([("x".into(), PolyExpr::state("x"))]);
    cmp_zero_arg.word_translation.entries[0].steps[0].arg_exprs = vec![clit(&q, 0)];
    let out_m05b = solve_transfer_task(
        &CheckedTransferTask::validate(TransferSpec {
            name: "m05_nl_solvable".into(),
            steps: vec![TransferStepSpec {
                name: "s".into(),
                comparison: cmp_zero_arg.clone(),
                source_phase: "Idle".into(),
                domain_laws: vec![],
                target_phase: "Idle".into(),
                lift_map: BTreeMap::from([
                    ("b".into(), PolyExpr::state("x")),
                    ("c".into(), clit(&q, 0)),
                ]),
                provenance: None,
            }],
            word_checks: vec![],
            old_word_lifts: vec![OldWordLiftSpec {
                name: "find_unit".into(),
                args: vec![],
                target_steps: vec![WordStepExpr {
                    operation: "apply".into(),
                    arg_exprs: vec![clit(&q, 0)],
                }],
                max_length: Some(1),
                provenance: None,
            }],
            change_spec: empty_cs(q.clone(), vec![]),
            eval_condition: None,
            require_full_domain: false,
            provenance: Provenance::new(vec![orig("m05b")], vec![MathClause::G140G2]),
        })
        .unwrap(),
    );
    assert_eq!(out_m05b.verdict, Verdict::Established);
    assert!(out_m05b.transfer.unwrap().old_word_lifts[0].lift_found);

    let mut cmp_sqrt2 = cmp_zero_arg;
    cmp_sqrt2.after.operations[0].domain_laws[0].polynomial =
        PolyExpr::pow(PolyExpr::arg("u"), 2) - clit(&q, 2);
    let spec_sqrt2 = TransferSpec {
        name: "m05c".into(),
        steps: vec![TransferStepSpec {
            name: "s".into(),
            comparison: cmp_sqrt2,
            source_phase: "Idle".into(),
            domain_laws: vec![],
            target_phase: "Idle".into(),
            lift_map: BTreeMap::from([
                ("b".into(), PolyExpr::state("x")),
                ("c".into(), clit(&q, 0)),
            ]),
            provenance: None,
        }],
        word_checks: vec![],
        old_word_lifts: vec![OldWordLiftSpec {
            name: "lift_const".into(),
            args: vec![],
            target_steps: vec![WordStepExpr {
                operation: "apply".into(),
                arg_exprs: vec![clit(&q, 0)],
            }],
            max_length: Some(1),
            provenance: None,
        }],
        change_spec: empty_cs(q.clone(), vec![]),
        eval_condition: None,
        require_full_domain: false,
        provenance: Provenance::new(vec![orig("m05c")], vec![MathClause::G140G2]),
    };
    let out_m05c = solve_transfer_task(&CheckedTransferTask::validate(spec_sqrt2).unwrap());
    assert!(matches!(out_m05c.verdict, Verdict::Undetermined(_)));

    let mut cmp_inv = pair_bc("X0", "X1", q.clone(), true);
    cmp_inv.after.operations[0].domain_laws = vec![StateLaw {
        name: "px".into(),
        kind: LawKind::Semantic,
        polynomial: PolyExpr::param("p") * PolyExpr::state("c"),
        provenance: None,
    }];
    cmp_inv.after.operations[0].updates.insert(
        "b".into(),
        PolyExpr::state("b") + PolyExpr::state("c") + PolyExpr::arg("u"),
    );
    cmp_inv.after.observations[0].components = vec![PolyExpr::state("b")];
    cmp_inv.state_comparisons[0].map = BTreeMap::from([("x".into(), PolyExpr::state("b"))]);
    let out_m05d = solve_transfer_task(
        &CheckedTransferTask::validate(TransferSpec {
            name: "m05d_eval_inv".into(),
            steps: vec![TransferStepSpec {
                name: "s".into(),
                comparison: cmp_inv,
                source_phase: "Idle".into(),
                domain_laws: vec![],
                target_phase: "Idle".into(),
                lift_map: BTreeMap::from([
                    ("b".into(), PolyExpr::state("x")),
                    ("c".into(), clit(&q, 0)),
                ]),
                provenance: None,
            }],
            word_checks: vec![WordCheckSpec {
                name: "apply_inv".into(),
                args: vec!["v".into()],
                steps: vec![WordStepExpr {
                    operation: "apply".into(),
                    arg_exprs: vec![PolyExpr::arg("v")],
                }],
                provenance: None,
            }],
            old_word_lifts: vec![],
            change_spec: empty_cs(q.clone(), vec!["p"]),
            eval_condition: Some(EvalCondition {
                name: "p_nz".into(),
                evaluations: vec![],
                equations: vec![],
                invertibles: vec![NamedPoly {
                    name: "p_unit".into(),
                    expr: PolyExpr::param("p"),
                    provenance: None,
                }],
                point_domain: PointDomain::AlgebraicClosure,
                provenance: Provenance::new(vec![orig("p_nz")], vec![MathClause::G141D5]),
            }),
            require_full_domain: false,
            provenance: Provenance::new(vec![orig("m05d")], vec![MathClause::G140G2]),
        })
        .unwrap(),
    );
    assert_eq!(out_m05d.verdict, Verdict::Established);
    let wc_m05d = &out_m05d.transfer.unwrap().word_checks[0];
    assert!(wc_m05d.domain_nonempty);
    assert!(wc_m05d.state_commutativity_matched);
}

#[test]
fn transfer_m06_fp_classification_and_q_remaining_nonlinear() {
    let fp = CoeffDomain::Fp(num_bigint::BigUint::from(5u32));
    let x0 = id_single_pres("F0", fp.clone(), vec![]);
    let x1 = id_single_pres("F1", fp.clone(), vec![]);
    let x2 = id_single_pres("F2", fp.clone(), vec![]);
    let fp_cmp = |a: &Presentation, b: &Presentation| ComparisonPair {
        before: a.clone(),
        after: b.clone(),
        state_comparisons: vec![StateComparison {
            after_phase: "S".into(),
            before_phase: "S".into(),
            map: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
            provenance: None,
        }],
        word_translation: WordTranslation { entries: vec![] },
    };
    let s1 = TransferStepSpec {
        name: "s1".into(),
        comparison: fp_cmp(&x0, &x1),
        source_phase: "S".into(),
        domain_laws: vec![StateLaw {
            name: "x1".into(),
            kind: LawKind::Semantic,
            polynomial: PolyExpr::state("x") - clit(&fp, 1),
            provenance: None,
        }],
        target_phase: "S".into(),
        lift_map: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
        provenance: None,
    };
    let s2_dup = TransferStepSpec {
        name: "s2".into(),
        comparison: fp_cmp(&x1, &x2),
        source_phase: "S".into(),
        domain_laws: vec![StateLaw {
            name: "x1_dup".into(),
            kind: LawKind::Semantic,
            polynomial: PolyExpr::state("x") - clit(&fp, 1),
            provenance: None,
        }],
        target_phase: "S".into(),
        lift_map: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
        provenance: None,
    };
    let s1_open = TransferStepSpec {
        domain_laws: vec![],
        ..s1.clone()
    };
    let out_fp_full = solve_transfer_task(
        &CheckedTransferTask::validate(TransferSpec {
            name: "m06_fp_full".into(),
            steps: vec![s1, s2_dup.clone()],
            word_checks: vec![],
            old_word_lifts: vec![],
            change_spec: empty_cs(fp.clone(), vec![]),
            eval_condition: None,
            require_full_domain: true,
            provenance: Provenance::new(vec![orig("m06fp")], vec![MathClause::G140G3]),
        })
        .unwrap(),
    );
    assert_eq!(out_fp_full.verdict, Verdict::Established);
    assert_eq!(
        out_fp_full.transfer.unwrap().domain_relation,
        DomainRelation::FullIsomorphic
    );

    let out_fp_proper = solve_transfer_task(
        &CheckedTransferTask::validate(TransferSpec {
            name: "m06_fp_proper".into(),
            steps: vec![s1_open.clone(), s2_dup.clone()],
            word_checks: vec![],
            old_word_lifts: vec![],
            change_spec: empty_cs(fp.clone(), vec![]),
            eval_condition: None,
            require_full_domain: false,
            provenance: Provenance::new(vec![orig("m06fpp")], vec![MathClause::G140G3]),
        })
        .unwrap(),
    );
    assert_eq!(out_fp_proper.verdict, Verdict::Established);
    assert_eq!(
        out_fp_proper.transfer.unwrap().domain_relation,
        DomainRelation::ProperSubdomain
    );
    assert_eq!(
        solve_transfer_task(
            &CheckedTransferTask::validate(TransferSpec {
                name: "m06_fp_proper_req".into(),
                steps: vec![s1_open, s2_dup],
                word_checks: vec![],
                old_word_lifts: vec![],
                change_spec: empty_cs(fp, vec![]),
                eval_condition: None,
                require_full_domain: true,
                provenance: Provenance::new(vec![orig("m06fppr")], vec![MathClause::G140G3]),
            })
            .unwrap(),
        )
        .verdict,
        Verdict::Refuted
    );

    let q = CoeffDomain::Q;
    let q0 = id_single_pres("Q0", q.clone(), vec![]);
    let q1 = id_single_pres("Q1", q.clone(), vec![]);
    let q2 = id_single_pres("Q2", q.clone(), vec![]);
    let q_cmp = |a: &Presentation, b: &Presentation| ComparisonPair {
        before: a.clone(),
        after: b.clone(),
        state_comparisons: vec![StateComparison {
            after_phase: "S".into(),
            before_phase: "S".into(),
            map: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
            provenance: None,
        }],
        word_translation: WordTranslation { entries: vec![] },
    };
    let out_q_nl = solve_transfer_task(
        &CheckedTransferTask::validate(TransferSpec {
            name: "m06_q_nl_full".into(),
            steps: vec![
                TransferStepSpec {
                    name: "s1".into(),
                    comparison: q_cmp(&q0, &q1),
                    source_phase: "S".into(),
                    domain_laws: vec![StateLaw {
                        name: "x0".into(),
                        kind: LawKind::Semantic,
                        polynomial: PolyExpr::state("x"),
                        provenance: None,
                    }],
                    target_phase: "S".into(),
                    lift_map: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
                    provenance: None,
                },
                TransferStepSpec {
                    name: "s2".into(),
                    comparison: q_cmp(&q1, &q2),
                    source_phase: "S".into(),
                    domain_laws: vec![StateLaw {
                        name: "nl_implied".into(),
                        kind: LawKind::Semantic,
                        polynomial: (PolyExpr::pow(PolyExpr::param("k"), 2) - clit(&q, 2))
                            * (PolyExpr::state("x") - clit(&q, 1)),
                        provenance: None,
                    }],
                    target_phase: "S".into(),
                    lift_map: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
                    provenance: None,
                },
            ],
            word_checks: vec![],
            old_word_lifts: vec![],
            change_spec: empty_cs(q.clone(), vec!["k"]),
            eval_condition: Some(EvalCondition {
                name: "k2m2".into(),
                evaluations: vec![],
                equations: vec![NamedPoly {
                    name: "k_eq".into(),
                    expr: PolyExpr::pow(PolyExpr::param("k"), 2) - clit(&q, 2),
                    provenance: None,
                }],
                invertibles: vec![],
                point_domain: PointDomain::AlgebraicClosure,
                provenance: Provenance::new(vec![orig("k2m2")], vec![MathClause::G141D5]),
            }),
            require_full_domain: true,
            provenance: Provenance::new(vec![orig("m06q")], vec![MathClause::G140G3]),
        })
        .unwrap(),
    );
    assert_eq!(out_q_nl.verdict, Verdict::Established);
    assert_eq!(
        out_q_nl.transfer.unwrap().domain_relation,
        DomainRelation::FullIsomorphic
    );
}
