use crate::ir::change::{ChangeSpec, EvalCondition, ParamDecl, PointDomain};
use crate::ir::presentation::{
    ComparisonPair, CoordDecl, LawKind, ObservationDecl, OperationDecl, PhaseDecl, Presentation,
    SortDecl, StateComparison, StateLaw, TranslatedStep, TranslatedWord, WordTranslation,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::result_ext::DomainRelation;
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::ir::transfer::{
    CheckedTransferTask, OldWordLiftSpec, TransferSpec, TransferStepSpec, WordCheckSpec,
    WordStepExpr,
};
use crate::solver::solve_transfer_task;
use std::collections::BTreeMap;

fn orig(id: &str) -> SourceRef {
    SourceRef::new(id, OriginKind::HumanAdopted).with_location(
        "transfer-test",
        "tr.law",
        Some((1, 20)),
    )
}

fn clit(d: &CoeffDomain, n: i64) -> PolyExpr {
    match d {
        CoeffDomain::Z => PolyExpr::int(n),
        CoeffDomain::Q => PolyExpr::rat(n, 1).expect("rat"),
        CoeffDomain::Fp(m) => {
            PolyExpr::Const(ScalarLit::fp(num_bigint::BigInt::from(n), m.clone()).expect("fp"))
        }
    }
}

fn empty_cs(domain: CoeffDomain, params: Vec<&str>) -> ChangeSpec {
    ChangeSpec {
        name: "H".into(),
        coeff_domain: domain.clone(),
        parameters: params
            .into_iter()
            .map(|n| ParamDecl {
                name: n.into(),
                coeff_domain: domain.clone(),
                provenance: None,
            })
            .collect(),
        fixed: vec![],
        editable: vec![],
        provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140G1]),
    }
}

fn pair_bc(name_old: &str, name_new: &str, domain: CoeffDomain, has_op: bool) -> ComparisonPair {
    let old_ops = if has_op {
        vec![OperationDecl {
            name: "apply".into(),
            source_phase: "Idle".into(),
            target_phase: "Idle".into(),
            args: vec![("u".into(), "D".into())],
            domain_laws: vec![],
            updates: BTreeMap::from([("x".into(), PolyExpr::state("x") + PolyExpr::arg("u"))]),
            provenance: None,
        }]
    } else {
        vec![]
    };
    let mut new_ops = vec![];
    let mut wt_entries = vec![];
    if has_op {
        new_ops.push(OperationDecl {
            name: "apply".into(),
            source_phase: "Idle".into(),
            target_phase: "Idle".into(),
            args: vec![("u".into(), "D".into())],
            domain_laws: vec![],
            updates: BTreeMap::from([
                ("b".into(), PolyExpr::state("b") + PolyExpr::arg("u")),
                ("c".into(), PolyExpr::state("c")),
            ]),
            provenance: None,
        });
        wt_entries.push(TranslatedWord {
            after_operation: "apply".into(),
            steps: vec![TranslatedStep {
                before_operation: "apply".into(),
                arg_exprs: vec![PolyExpr::arg("u")],
            }],
            provenance: None,
        });
    }
    let old = Presentation {
        name: name_old.into(),
        coeff_domain: domain.clone(),
        sorts: vec![SortDecl {
            name: "D".into(),
            rank: 1,
            coeff_domain: domain.clone(),
            provenance: Some(orig("d")),
        }],
        phases: vec![PhaseDecl {
            name: "Idle".into(),
            coords: vec![CoordDecl::symbolic("x", "D")],
            state_laws: vec![],
            provenance: None,
        }],
        operations: old_ops,
        observations: vec![ObservationDecl {
            name: "read".into(),
            phase: "Idle".into(),
            components: vec![PolyExpr::state("x")],
            provenance: None,
        }],
        provenance: Provenance::new(vec![orig(name_old)], vec![MathClause::G140G1]),
    };
    let new = Presentation {
        name: name_new.into(),
        coeff_domain: domain.clone(),
        sorts: vec![SortDecl {
            name: "D".into(),
            rank: 1,
            coeff_domain: domain,
            provenance: Some(orig("d")),
        }],
        phases: vec![PhaseDecl {
            name: "Idle".into(),
            coords: vec![CoordDecl::symbolic("b", "D"), CoordDecl::symbolic("c", "D")],
            state_laws: vec![],
            provenance: None,
        }],
        operations: new_ops,
        observations: vec![ObservationDecl {
            name: "read".into(),
            phase: "Idle".into(),
            components: vec![PolyExpr::state("b") + PolyExpr::state("c")],
            provenance: None,
        }],
        provenance: Provenance::new(vec![orig(name_new)], vec![MathClause::G140G1]),
    };
    ComparisonPair {
        before: old,
        after: new,
        state_comparisons: vec![StateComparison {
            after_phase: "Idle".into(),
            before_phase: "Idle".into(),
            map: BTreeMap::from([("x".into(), PolyExpr::state("b") + PolyExpr::state("c"))]),
            provenance: None,
        }],
        word_translation: WordTranslation {
            entries: wt_entries,
        },
    }
}

#[test]
fn transfer_g1_lift_and_g2_word_check_and_old_lift() {
    let q = CoeffDomain::Q;
    let cmp = pair_bc("X0", "X1", q.clone(), true);
    let ok_spec = TransferSpec {
        name: "g1_lift_and_words".into(),
        steps: vec![TransferStepSpec {
            name: "s01".into(),
            comparison: cmp.clone(),
            source_phase: "Idle".into(),
            domain_laws: vec![],
            target_phase: "Idle".into(),
            lift_map: BTreeMap::from([
                ("b".into(), PolyExpr::state("x") + PolyExpr::param("k")),
                ("c".into(), clit(&q, 0)),
            ]),
            provenance: None,
        }],
        word_checks: vec![WordCheckSpec {
            name: "apply_u".into(),
            args: vec!["u".into()],
            steps: vec![WordStepExpr {
                operation: "apply".into(),
                arg_exprs: vec![PolyExpr::arg("u")],
            }],
            provenance: None,
        }],
        old_word_lifts: vec![],
        change_spec: empty_cs(q.clone(), vec!["k"]),
        eval_condition: None,
        require_full_domain: false,
        provenance: Provenance::new(
            vec![orig("g1")],
            vec![MathClause::G140G1, MathClause::G140G2],
        ),
    };
    let out_ok = solve_transfer_task(&CheckedTransferTask::validate(ok_spec).unwrap());
    assert_eq!(out_ok.verdict, Verdict::Established);
    let td = out_ok.transfer.unwrap();
    assert_eq!(td.domain_relation, DomainRelation::FullIsomorphic);
    assert!(td.restored_transfer.unwrap().reeval.matched);
    assert!(td.word_checks[0].domain_nonempty);
    assert!(td.word_checks[0].state_commutativity_matched);
    assert!(td.word_checks[0].observation_preserved);

    let mut cmp_fake = cmp.clone();
    cmp_fake.before.phases[0]
        .coords
        .push(CoordDecl::symbolic("z", "D"));
    cmp_fake.before.operations[0]
        .updates
        .insert("z".into(), PolyExpr::state("z"));
    cmp_fake.after.phases[0].coords =
        vec![CoordDecl::symbolic("x", "D"), CoordDecl::symbolic("z", "D")];
    cmp_fake.after.operations[0].updates = BTreeMap::from([
        ("x".into(), PolyExpr::state("x") + PolyExpr::arg("u")),
        ("z".into(), PolyExpr::state("z")),
    ]);
    cmp_fake.after.observations[0].components = vec![PolyExpr::state("x")];
    cmp_fake.state_comparisons[0].map = BTreeMap::from([
        ("x".into(), PolyExpr::state("x")),
        ("z".into(), PolyExpr::state("z")),
    ]);
    let fake_spec = TransferSpec {
        name: "obs_only_fake_lift".into(),
        steps: vec![TransferStepSpec {
            name: "bad_lift".into(),
            comparison: cmp_fake,
            source_phase: "Idle".into(),
            domain_laws: vec![],
            target_phase: "Idle".into(),
            lift_map: BTreeMap::from([
                ("x".into(), PolyExpr::state("x")),
                ("z".into(), PolyExpr::state("z") + clit(&q, 1)),
            ]),
            provenance: None,
        }],
        word_checks: vec![],
        old_word_lifts: vec![],
        change_spec: empty_cs(q.clone(), vec![]),
        eval_condition: None,
        require_full_domain: false,
        provenance: Provenance::new(vec![orig("fake")], vec![MathClause::G140G1]),
    };
    assert_eq!(
        solve_transfer_task(&CheckedTransferTask::validate(fake_spec).unwrap()).verdict,
        Verdict::Refuted
    );

    let mut cmp_owl = cmp;
    cmp_owl.after.operations[0].updates = BTreeMap::from([
        (
            "b".into(),
            PolyExpr::state("b") + clit(&q, 2) * PolyExpr::arg("u"),
        ),
        ("c".into(), PolyExpr::state("c")),
    ]);
    cmp_owl.word_translation.entries[0].steps[0].arg_exprs = vec![clit(&q, 2) * PolyExpr::arg("u")];
    cmp_owl.before.operations.push(OperationDecl {
        name: "reset".into(),
        source_phase: "Idle".into(),
        target_phase: "Idle".into(),
        args: vec![],
        domain_laws: vec![],
        updates: BTreeMap::from([("x".into(), clit(&q, 0))]),
        provenance: None,
    });
    let owl_spec = TransferSpec {
        name: "old_word_lifts".into(),
        steps: vec![TransferStepSpec {
            name: "s01".into(),
            comparison: cmp_owl,
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
        old_word_lifts: vec![
            OldWordLiftSpec {
                name: "find_apply_shift".into(),
                args: vec!["v".into()],
                target_steps: vec![WordStepExpr {
                    operation: "apply".into(),
                    arg_exprs: vec![clit(&q, 2) * PolyExpr::arg("v")],
                }],
                max_length: Some(1),
                provenance: None,
            },
            OldWordLiftSpec {
                name: "no_reset_lift".into(),
                args: vec![],
                target_steps: vec![WordStepExpr {
                    operation: "reset".into(),
                    arg_exprs: vec![],
                }],
                max_length: Some(2),
                provenance: None,
            },
        ],
        change_spec: empty_cs(q, vec![]),
        eval_condition: None,
        require_full_domain: false,
        provenance: Provenance::new(vec![orig("owl")], vec![MathClause::G140G2]),
    };
    let out_owl = solve_transfer_task(&CheckedTransferTask::validate(owl_spec).unwrap());
    assert_eq!(out_owl.verdict, Verdict::Established);
    let owls = out_owl.transfer.unwrap().old_word_lifts;
    assert!(
        owls[0].lift_found,
        "expected lift for apply(2*v), got {:?}",
        owls[0]
    );
    assert!(
        !owls[1].lift_found,
        "expected no lift for unrepresented reset"
    );
}

#[test]
fn transfer_g3_composition_full_proper_empty_and_three_step() {
    let q = CoeffDomain::Q;
    let make_id_pres = |name: &str| Presentation {
        name: name.into(),
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
        operations: vec![],
        observations: vec![ObservationDecl {
            name: "read".into(),
            phase: "S".into(),
            components: vec![PolyExpr::state("x")],
            provenance: None,
        }],
        provenance: Provenance::new(vec![orig(name)], vec![MathClause::G140G3]),
    };
    let x0 = make_id_pres("X0");
    let x1 = make_id_pres("X1");
    let x2 = make_id_pres("X2");
    let x3 = make_id_pres("X3");
    let id_cmp = |a: &Presentation, b: &Presentation| ComparisonPair {
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

    let step01_full = TransferStepSpec {
        name: "s01".into(),
        comparison: id_cmp(&x0, &x1),
        source_phase: "S".into(),
        domain_laws: vec![StateLaw {
            name: "d0".into(),
            kind: LawKind::Semantic,
            polynomial: PolyExpr::state("x") - clit(&q, 1),
            provenance: None,
        }],
        target_phase: "S".into(),
        lift_map: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
        provenance: None,
    };
    let step12_full = TransferStepSpec {
        name: "s12".into(),
        comparison: id_cmp(&x1, &x2),
        source_phase: "S".into(),
        domain_laws: vec![StateLaw {
            name: "d1".into(),
            kind: LawKind::Semantic,
            polynomial: PolyExpr::state("x") - clit(&q, 1),
            provenance: None,
        }],
        target_phase: "S".into(),
        lift_map: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
        provenance: None,
    };
    let out_full = solve_transfer_task(
        &CheckedTransferTask::validate(TransferSpec {
            name: "full_3step".into(),
            steps: vec![
                step01_full.clone(),
                step12_full.clone(),
                TransferStepSpec {
                    name: "s23".into(),
                    comparison: id_cmp(&x2, &x3),
                    source_phase: "S".into(),
                    domain_laws: vec![StateLaw {
                        name: "d2".into(),
                        kind: LawKind::Semantic,
                        polynomial: PolyExpr::state("x") - clit(&q, 1),
                        provenance: None,
                    }],
                    target_phase: "S".into(),
                    lift_map: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
                    provenance: None,
                },
            ],
            word_checks: vec![],
            old_word_lifts: vec![],
            change_spec: empty_cs(q.clone(), vec![]),
            eval_condition: None,
            require_full_domain: true,
            provenance: Provenance::new(vec![orig("g3f")], vec![MathClause::G140G3]),
        })
        .unwrap(),
    );
    assert_eq!(out_full.verdict, Verdict::Established);
    assert_eq!(
        out_full.transfer.unwrap().domain_relation,
        DomainRelation::FullIsomorphic
    );

    let step01_open = TransferStepSpec {
        domain_laws: vec![],
        ..step01_full.clone()
    };
    let step12_sub = TransferStepSpec {
        domain_laws: vec![StateLaw {
            name: "d1".into(),
            kind: LawKind::Semantic,
            polynomial: PolyExpr::state("x") - clit(&q, 2),
            provenance: None,
        }],
        ..step12_full.clone()
    };
    let out_proper = solve_transfer_task(
        &CheckedTransferTask::validate(TransferSpec {
            name: "proper_sub".into(),
            steps: vec![step01_open.clone(), step12_sub.clone()],
            word_checks: vec![],
            old_word_lifts: vec![],
            change_spec: empty_cs(q.clone(), vec![]),
            eval_condition: None,
            require_full_domain: false,
            provenance: Provenance::new(vec![orig("g3p")], vec![MathClause::G140G3]),
        })
        .unwrap(),
    );
    assert_eq!(out_proper.verdict, Verdict::Established);
    assert_eq!(
        out_proper.transfer.unwrap().domain_relation,
        DomainRelation::ProperSubdomain
    );

    let out_proper_req = solve_transfer_task(
        &CheckedTransferTask::validate(TransferSpec {
            name: "proper_req_full".into(),
            steps: vec![step01_open, step12_sub],
            word_checks: vec![],
            old_word_lifts: vec![],
            change_spec: empty_cs(q.clone(), vec![]),
            eval_condition: None,
            require_full_domain: true,
            provenance: Provenance::new(vec![orig("g3pr")], vec![MathClause::G140G3]),
        })
        .unwrap(),
    );
    assert_eq!(out_proper_req.verdict, Verdict::Refuted);

    let step12_disjoint = TransferStepSpec {
        domain_laws: vec![StateLaw {
            name: "d1".into(),
            kind: LawKind::Semantic,
            polynomial: PolyExpr::state("x") - clit(&q, 2),
            provenance: None,
        }],
        ..step12_full
    };
    let out_empty = solve_transfer_task(
        &CheckedTransferTask::validate(TransferSpec {
            name: "empty_pullback".into(),
            steps: vec![step01_full, step12_disjoint],
            word_checks: vec![],
            old_word_lifts: vec![],
            change_spec: empty_cs(q, vec![]),
            eval_condition: None,
            require_full_domain: false,
            provenance: Provenance::new(vec![orig("g3e")], vec![MathClause::G140G3]),
        })
        .unwrap(),
    );
    assert_eq!(out_empty.verdict, Verdict::Established);
    assert_eq!(
        out_empty.transfer.unwrap().domain_relation,
        DomainRelation::Empty
    );
}

#[test]
fn transfer_p53_busy_state_rejected_and_silence_boundaries() {
    let q = CoeffDomain::Q;
    let make_busy = |name: &str, mu: i64, rho: i64| Presentation {
        name: name.into(),
        coeff_domain: q.clone(),
        sorts: vec![SortDecl {
            name: "D".into(),
            rank: 1,
            coeff_domain: q.clone(),
            provenance: Some(orig("d")),
        }],
        phases: vec![PhaseDecl {
            name: "Busy".into(),
            coords: vec![
                CoordDecl::symbolic("B", "D"),
                CoordDecl::symbolic("C", "D"),
                CoordDecl::symbolic("h", "D"),
            ],
            state_laws: vec![StateLaw {
                name: "busy_law".into(),
                kind: LawKind::Representation,
                polynomial: clit(&q, mu * (1 - rho))
                    * (PolyExpr::state("h") - PolyExpr::state("C")),
                provenance: None,
            }],
            provenance: None,
        }],
        operations: vec![],
        observations: vec![ObservationDecl {
            name: "read".into(),
            phase: "Busy".into(),
            components: vec![PolyExpr::state("B") + PolyExpr::state("C")],
            provenance: None,
        }],
        provenance: Provenance::new(vec![orig(name)], vec![MathClause::G140P5Dot3]),
    };
    let x0 = make_busy("M_100", 0, 0);
    let x1 = make_busy("M_000", 0, 0);
    let x2 = make_busy("M_010", 1, 0);
    let id_busy = |a: &Presentation, b: &Presentation| ComparisonPair {
        before: a.clone(),
        after: b.clone(),
        state_comparisons: vec![StateComparison {
            after_phase: "Busy".into(),
            before_phase: "Busy".into(),
            map: BTreeMap::from([
                ("B".into(), PolyExpr::state("B")),
                ("C".into(), PolyExpr::state("C")),
                ("h".into(), PolyExpr::state("h")),
            ]),
            provenance: None,
        }],
        word_translation: WordTranslation { entries: vec![] },
    };
    let busy_pt_laws = vec![
        StateLaw {
            name: "b0".into(),
            kind: LawKind::Semantic,
            polynomial: PolyExpr::state("B"),
            provenance: None,
        },
        StateLaw {
            name: "c1".into(),
            kind: LawKind::Semantic,
            polynomial: PolyExpr::state("C") - clit(&q, 1),
            provenance: None,
        },
        StateLaw {
            name: "h0".into(),
            kind: LawKind::Semantic,
            polynomial: PolyExpr::state("h"),
            provenance: None,
        },
    ];
    let p53_spec = TransferSpec {
        name: "p53_busy_transfer".into(),
        steps: vec![
            TransferStepSpec {
                name: "step1".into(),
                comparison: id_busy(&x0, &x1),
                source_phase: "Busy".into(),
                domain_laws: busy_pt_laws.clone(),
                target_phase: "Busy".into(),
                lift_map: BTreeMap::from([
                    ("B".into(), PolyExpr::state("B")),
                    ("C".into(), PolyExpr::state("C")),
                    ("h".into(), PolyExpr::state("h")),
                ]),
                provenance: None,
            },
            TransferStepSpec {
                name: "step2".into(),
                comparison: id_busy(&x1, &x2),
                source_phase: "Busy".into(),
                domain_laws: busy_pt_laws,
                target_phase: "Busy".into(),
                lift_map: BTreeMap::from([
                    ("B".into(), PolyExpr::state("B")),
                    ("C".into(), PolyExpr::state("C")),
                    ("h".into(), PolyExpr::state("h")),
                ]),
                provenance: None,
            },
        ],
        word_checks: vec![],
        old_word_lifts: vec![],
        change_spec: empty_cs(q.clone(), vec![]),
        eval_condition: None,
        require_full_domain: false,
        provenance: Provenance::new(vec![orig("p53")], vec![MathClause::G140P5Dot3]),
    };

    let out_p53 = solve_transfer_task(&CheckedTransferTask::validate(p53_spec).unwrap());
    assert_eq!(out_p53.verdict, Verdict::Refuted);
    assert!(out_p53.empty_witness.is_some());
    let diags = out_p53.transfer.unwrap().step_diagnostics;
    assert!(
        diags[1].target_law_residuals.iter().any(|r| r == "-1"),
        "diags={diags:?}"
    );

    let unb_spec = TransferSpec {
        name: "unbounded_lift".into(),
        steps: vec![TransferStepSpec {
            name: "s".into(),
            comparison: pair_bc("X0", "X1", q.clone(), true),
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
            name: "unbounded".into(),
            args: vec![],
            target_steps: vec![WordStepExpr {
                operation: "apply".into(),
                arg_exprs: vec![clit(&q, 1)],
            }],
            max_length: None,
            provenance: None,
        }],
        change_spec: empty_cs(q, vec![]),
        eval_condition: None,
        require_full_domain: false,
        provenance: Provenance::new(vec![orig("unb")], vec![MathClause::G140G2]),
    };
    assert!(matches!(
        solve_transfer_task(&CheckedTransferTask::validate(unb_spec).unwrap()).verdict,
        Verdict::Undetermined(SilenceReason::UnboundedSearchOutOfScope { .. })
    ));

    let mut cmp_zq = pair_bc("Z0", "Z1", CoeffDomain::Z, true);
    cmp_zq.after.phases[0].state_laws.push(StateLaw {
        name: "c0".into(),
        kind: LawKind::Representation,
        polynomial: PolyExpr::state("c"),
        provenance: None,
    });
    cmp_zq.after.operations[0]
        .updates
        .insert("c".into(), PolyExpr::state("c"));
    let z_quot_spec = TransferSpec {
        name: "z_param_quot".into(),
        steps: vec![TransferStepSpec {
            name: "s".into(),
            comparison: cmp_zq,
            source_phase: "Idle".into(),
            domain_laws: vec![],
            target_phase: "Idle".into(),
            lift_map: BTreeMap::from([
                ("b".into(), PolyExpr::state("x") + PolyExpr::param("k")),
                ("c".into(), PolyExpr::int(0)),
            ]),
            provenance: None,
        }],
        word_checks: vec![],
        old_word_lifts: vec![],
        change_spec: empty_cs(CoeffDomain::Z, vec!["k"]),
        eval_condition: Some(EvalCondition {
            name: "zpts".into(),
            evaluations: vec![],
            equations: vec![],
            invertibles: vec![],
            point_domain: PointDomain::IntegerPoints,
            provenance: Provenance::new(vec![orig("zq")], vec![MathClause::G141D5]),
        }),
        require_full_domain: false,
        provenance: Provenance::new(vec![orig("zq")], vec![MathClause::G141D5]),
    };
    assert!(matches!(
        solve_transfer_task(&CheckedTransferTask::validate(z_quot_spec).unwrap()).verdict,
        Verdict::Undetermined(SilenceReason::QuotientIdealOutOfScope { .. })
    ));
}
