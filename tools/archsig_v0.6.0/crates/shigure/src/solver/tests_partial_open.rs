//! 第18章後半（開領域局所網羅・定理 18.18・非適用境界・強 Kleene 引数順序）の単体テスト。

use super::partial_eval::solve_partial_task;
use crate::ir::partial::{
    AffinePartialPresentation, AffineRestrictionSpec, FiberCoverageCheckSpec,
    FinitePartialPresentation, OpenDomainSpec, OpenOpTable, OpenRelTable, PartialEvalLawSpec,
    PartialFormula, PartialOpSignature, PartialPredSignature, PartialRecordKind, PartialRecordSpec,
    PartialRepresentation, PartialSlotDecl, PartialTaskSpec, PartialTerm, PartialTruth,
    validate_partial_task,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::term::{CoeffDomain, ScalarLit};
use std::collections::{BTreeMap, BTreeSet};

fn prov() -> Provenance {
    Provenance::new(
        vec![SourceRef::new("ch18_open_test", OriginKind::StaticAnalysis)],
        vec![MathClause::AatCh18Thm18Dot16],
    )
}

#[test]
fn ch18_open_domain_example18_15_thm18_16_and_thm18_18_affine_unique_repair() {
    // 数学本文 例 18.15: ∀x ∃y R(x,y), A_0 = {a}, R_{A_0} = ∅; A = {a,b}, R_A = {(a,b),(b,a)}
    // 正の式自体は A_0 で偽、A で真（positive_preserved）。
    // ファイバー網羅 rho(a0)=b0, rho(a1)=b1 vs rho(a1)=b0（式 18.5 p_A^{-1}(B) ⊆ X_s(A_0)）の両向きを検査。
    let open_spec = PartialTaskSpec {
        name: "ex_18_15_open".into(),
        representation: PartialRepresentation::FiniteTable(FinitePartialPresentation {
            sorts: BTreeMap::from([("V".into(), vec!["0".into()])]),
            operations: vec![],
            relations: vec![],
            slots: vec![],
            background_constraints: vec![],
            records: vec![],
            max_completions: 8,
        }),
        eval_laws: vec![],
        quantifier_spec: None,
        open_domain: Some(OpenDomainSpec {
            substructure_carriers: BTreeMap::from([
                ("A".into(), vec!["a0".into()]),
                ("B".into(), vec!["b0".into()]),
            ]),
            ambient_carriers: BTreeMap::from([
                ("A".into(), vec!["a0".into(), "a1".into()]),
                ("B".into(), vec!["b0".into(), "b1".into()]),
            ]),
            substructure_ops: vec![OpenOpTable {
                name: "rho".into(),
                arg_sorts: vec!["A".into()],
                out_sort: "B".into(),
                entries: BTreeMap::from([(vec!["a0".into()], Some("b0".into()))]),
            }],
            ambient_ops: vec![OpenOpTable {
                name: "rho".into(),
                arg_sorts: vec!["A".into()],
                out_sort: "B".into(),
                entries: BTreeMap::from([
                    (vec!["a0".into()], Some("b0".into())),
                    (vec!["a1".into()], Some("b1".into())),
                ]),
            }],
            substructure_rels: vec![OpenRelTable {
                name: "R".into(),
                arg_sorts: vec!["A".into(), "A".into()],
                entries: BTreeSet::new(),
            }],
            ambient_rels: vec![OpenRelTable {
                name: "R".into(),
                arg_sorts: vec!["A".into(), "A".into()],
                entries: BTreeSet::from([
                    vec!["a0".into(), "a1".into()],
                    vec!["a1".into(), "a0".into()],
                ]),
            }],
            fiber_checks: vec![FiberCoverageCheckSpec {
                op_name: "rho".into(),
                arg_sort: "A".into(),
                target_sort: "B".into(),
                known_targets: vec!["b0".into()],
            }],
            positive_or_law: PartialEvalLawSpec {
                name: "forall_exists_R".into(),
                antecedent: None,
                conclusion: PartialFormula::Forall {
                    var: "x".into(),
                    sort: "A".into(),
                    restricted_domain: None,
                    body: Box::new(PartialFormula::Exists {
                        var: "y".into(),
                        sort: "A".into(),
                        restricted_domain: None,
                        body: Box::new(PartialFormula::Rel {
                            rel_name: "R".into(),
                            args: vec![PartialTerm::Var("x".into()), PartialTerm::Var("y".into())],
                        }),
                    }),
                },
                is_required_law: false,
            },
            // 定理 18.18 Case A: M = [1, 1], b = [2], R = [1, 0] -> img_dim=1, fiber_dim=0 -> 大域唯一ではない
            affine_restriction: Some(AffineRestrictionSpec {
                coeff_domain: CoeffDomain::Q,
                m_matrix: vec![vec![
                    ScalarLit::rat(1, 1).unwrap(),
                    ScalarLit::rat(1, 1).unwrap(),
                ]],
                b_rhs: vec![ScalarLit::rat(2, 1).unwrap()],
                r_matrix: vec![vec![
                    ScalarLit::rat(1, 1).unwrap(),
                    ScalarLit::rat(0, 1).unwrap(),
                ]],
                num_vars: 2,
            }),
        }),
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    let out = solve_partial_task(&validate_partial_task(open_spec.clone()).unwrap());
    assert_eq!(out.verdict, Verdict::Established);
    let od = out.partial.unwrap().open_domain.unwrap();
    assert!(od.is_full_substructure);
    // p_A^{-1}({b0}) = {a0} ⊆ {a0} = X_A(A_0) より局所網羅成立
    assert!(od.all_fibers_locally_exhaustive);
    assert!(od.uncovered_fibers.is_empty());
    assert_eq!(od.sub_law_eval, "false");
    assert_eq!(od.ambient_law_eval, "true");
    assert!(od.positive_preserved);
    assert!(!od.law_evaluations_match);
    assert_eq!(od.affine_unique_repair_exists, Some(false));
    assert_eq!(od.affine_image_dim, Some(1));
    assert_eq!(od.affine_fiber_dim, Some(0));
    assert!(
        od.reevaluation
            .as_ref()
            .is_some_and(|r| r.checked && r.matched)
    );

    // 非正の式 (∀x ¬R(x, a0)) が A_0 で真・A で偽でも reevaluation.matched == true となること
    // かつ a1 -> b0 により p_A^{-1}({b0}) = {a0, a1} ⊈ X_A(A_0) で局所網羅失敗
    let mut non_exhaustive = open_spec.clone();
    let od_mut = non_exhaustive.open_domain.as_mut().unwrap();
    od_mut.ambient_ops[0]
        .entries
        .insert(vec!["a1".into()], Some("b0".into()));
    od_mut.positive_or_law.conclusion = PartialFormula::Forall {
        var: "x".into(),
        sort: "A".into(),
        restricted_domain: None,
        body: Box::new(PartialFormula::Not(Box::new(PartialFormula::Rel {
            rel_name: "R".into(),
            args: vec![
                PartialTerm::Var("x".into()),
                PartialTerm::Const("a0".into()),
            ],
        }))),
    };
    let out_ne = solve_partial_task(&validate_partial_task(non_exhaustive).unwrap());
    let od_ne = out_ne.partial.unwrap().open_domain.unwrap();
    assert!(!od_ne.all_fibers_locally_exhaustive);
    assert_eq!(od_ne.uncovered_fibers, vec!["rho(a1)"]);
    assert_eq!(od_ne.sub_law_eval, "true");
    assert_eq!(od_ne.ambient_law_eval, "false");
    assert!(!od_ne.positive_preserved);
    assert!(
        od_ne
            .reevaluation
            .as_ref()
            .is_some_and(|r| r.checked && r.matched)
    );

    // 定理 18.18 Case B (img_dim=0, fiber_dim=1 => false) と Case C (img_dim=0, fiber_dim=0 => true)
    let mut case_b = open_spec.clone();
    case_b
        .open_domain
        .as_mut()
        .unwrap()
        .affine_restriction
        .as_mut()
        .unwrap()
        .r_matrix = vec![vec![
        ScalarLit::rat(1, 1).unwrap(),
        ScalarLit::rat(1, 1).unwrap(),
    ]];
    let od_b = solve_partial_task(&validate_partial_task(case_b).unwrap())
        .partial
        .unwrap()
        .open_domain
        .unwrap();
    assert_eq!(od_b.affine_image_dim, Some(0));
    assert_eq!(od_b.affine_fiber_dim, Some(1));
    assert_eq!(od_b.affine_unique_repair_exists, Some(false));

    let mut case_c = open_spec;
    let ar_c = case_c
        .open_domain
        .as_mut()
        .unwrap()
        .affine_restriction
        .as_mut()
        .unwrap();
    ar_c.m_matrix = vec![
        vec![ScalarLit::rat(1, 1).unwrap(), ScalarLit::rat(0, 1).unwrap()],
        vec![ScalarLit::rat(0, 1).unwrap(), ScalarLit::rat(1, 1).unwrap()],
    ];
    ar_c.b_rhs = vec![ScalarLit::rat(2, 1).unwrap(), ScalarLit::rat(3, 1).unwrap()];
    ar_c.r_matrix = vec![vec![
        ScalarLit::rat(1, 1).unwrap(),
        ScalarLit::rat(0, 1).unwrap(),
    ]];
    let od_c = solve_partial_task(&validate_partial_task(case_c).unwrap())
        .partial
        .unwrap()
        .open_domain
        .unwrap();
    assert_eq!(od_c.affine_image_dim, Some(0));
    assert_eq!(od_c.affine_fiber_dim, Some(0));
    assert_eq!(od_c.affine_unique_repair_exists, Some(true));
}

#[test]
fn ch18_undetermined_on_unsupported_class_unobserved_and_max_completions() {
    let unsupported = PartialTaskSpec {
        name: "unsup".into(),
        representation: PartialRepresentation::UnsupportedClass {
            description: "polynomial_deg_3".into(),
        },
        eval_laws: vec![],
        quantifier_spec: None,
        open_domain: None,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    assert!(matches!(
        solve_partial_task(&validate_partial_task(unsupported).unwrap()).verdict,
        Verdict::Undetermined(SilenceReason::UnsupportedCompletionClass { .. })
    ));

    let unobs = PartialTaskSpec {
        name: "unobs".into(),
        representation: PartialRepresentation::FiniteTable(FinitePartialPresentation {
            sorts: BTreeMap::from([("V".into(), vec!["0".into()])]),
            operations: vec![],
            relations: vec![],
            slots: vec![],
            background_constraints: vec![],
            records: vec![],
            max_completions: 8,
        }),
        eval_laws: vec![],
        quantifier_spec: None,
        open_domain: None,
        provenance: prov(),
        undeclared_unobserved_slots: vec!["raw_unobserved".into()],
    };
    assert!(matches!(
        solve_partial_task(&validate_partial_task(unobs).unwrap()).verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { .. })
    ));

    let bounded = PartialTaskSpec {
        name: "max_comp_exceeded".into(),
        representation: PartialRepresentation::FiniteTable(FinitePartialPresentation {
            sorts: BTreeMap::from([("V".into(), vec!["0".into(), "1".into()])]),
            operations: vec![],
            relations: vec![],
            slots: vec![
                PartialSlotDecl {
                    name: "s1".into(),
                    sort: "V".into(),
                    domain_values: vec!["0".into(), "1".into()],
                },
                PartialSlotDecl {
                    name: "s2".into(),
                    sort: "V".into(),
                    domain_values: vec!["0".into(), "1".into()],
                },
            ],
            background_constraints: vec![],
            records: vec![],
            max_completions: 2,
        }),
        eval_laws: vec![],
        quantifier_spec: None,
        open_domain: None,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    assert!(matches!(
        solve_partial_task(&validate_partial_task(bounded).unwrap()).verdict,
        Verdict::Undetermined(SilenceReason::FiniteEnumerationOutOfScope { .. })
    ));

    // Relation 記録の衝突でも部分集合判定で正しい MUS が抽出・検算されることを確認
    let rel_mus = PartialTaskSpec {
        name: "rel_mus".into(),
        representation: PartialRepresentation::FiniteTable(FinitePartialPresentation {
            sorts: BTreeMap::from([("V".into(), vec!["0".into()])]),
            operations: vec![],
            relations: vec![PartialPredSignature {
                name: "R".into(),
                arg_sorts: vec!["V".into()],
            }],
            slots: vec![],
            background_constraints: vec![],
            records: vec![
                PartialRecordSpec {
                    id: "rel_pos".into(),
                    kind: PartialRecordKind::Relation {
                        rel_name: "R".into(),
                        args: vec!["0".into()],
                        holds: PartialTruth::True,
                    },
                },
                PartialRecordSpec {
                    id: "rel_neg".into(),
                    kind: PartialRecordKind::Relation {
                        rel_name: "R".into(),
                        args: vec!["0".into()],
                        holds: PartialTruth::ExplicitAbsent,
                    },
                },
            ],
            max_completions: 16,
        }),
        eval_laws: vec![],
        quantifier_spec: None,
        open_domain: None,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    let rel_out = solve_partial_task(&validate_partial_task(rel_mus).unwrap());
    assert_eq!(rel_out.verdict, Verdict::Refuted);
    let rp = rel_out.partial.unwrap();
    assert!(!rp.completion_consistent);
    assert!(rp.mus_verified);
    assert_eq!(
        rp.minimal_inconsistent_subsets,
        vec![vec!["rel_neg".to_owned(), "rel_pos".to_owned()]]
    );

    // 非真偽値スロット参照 (PartialTruth::UnobservedSlot) は黙示 true にならず整合しない
    let non_bool_slot = PartialTaskSpec {
        name: "non_bool_slot".into(),
        representation: PartialRepresentation::FiniteTable(FinitePartialPresentation {
            sorts: BTreeMap::from([("V".into(), vec!["abc".into()])]),
            operations: vec![],
            relations: vec![PartialPredSignature {
                name: "R".into(),
                arg_sorts: vec!["V".into()],
            }],
            slots: vec![PartialSlotDecl {
                name: "s".into(),
                sort: "V".into(),
                domain_values: vec!["abc".into()],
            }],
            background_constraints: vec![],
            records: vec![PartialRecordSpec {
                id: "r_nonbool".into(),
                kind: PartialRecordKind::Relation {
                    rel_name: "R".into(),
                    args: vec!["abc".into()],
                    holds: PartialTruth::UnobservedSlot("s".into()),
                },
            }],
            max_completions: 8,
        }),
        eval_laws: vec![],
        quantifier_spec: None,
        open_domain: None,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    let non_bool_out = solve_partial_task(&validate_partial_task(non_bool_slot).unwrap());
    assert_eq!(non_bool_out.verdict, Verdict::Refuted);
    assert!(!non_bool_out.partial.unwrap().completion_consistent);

    // アフィン評価方程式 (eval_equations) が supervaluation == "false" なら Verdict::Refuted
    let aff_eval_false = PartialTaskSpec {
        name: "aff_eval_false".into(),
        representation: PartialRepresentation::Affine(AffinePartialPresentation {
            coeff_domain: CoeffDomain::Q,
            coord_names: vec!["t".into()],
            x0: vec![ScalarLit::rat(0, 1).unwrap()],
            direction_t: vec![vec![ScalarLit::rat(1, 1).unwrap()]],
            background_rows: vec![],
            record_rows: vec![(
                "pin".into(),
                vec![ScalarLit::rat(1, 1).unwrap()],
                ScalarLit::rat(1, 1).unwrap(),
            )],
            eval_equations: vec![(
                "must_hold_eq".into(),
                vec![ScalarLit::rat(1, 1).unwrap()],
                ScalarLit::rat(0, 1).unwrap(),
            )],
        }),
        eval_laws: vec![],
        quantifier_spec: None,
        open_domain: None,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    let aff_false_out = solve_partial_task(&validate_partial_task(aff_eval_false).unwrap());
    assert_eq!(aff_false_out.verdict, Verdict::Refuted);
    let aff_p = aff_false_out.partial.unwrap();
    assert!(aff_p.completion_consistent);
    assert_eq!(aff_p.law_evaluations[0].supervaluation, "false");

    // 第1引数が Unknown、第2引数が ExplicitAbsent のとき早期 return せず厳密に false となる（max_completions=0 は既定値）
    let strict_order = PartialTaskSpec {
        name: "kleene_strict_arg_order".into(),
        representation: PartialRepresentation::FiniteTable(FinitePartialPresentation {
            sorts: BTreeMap::from([("V".into(), vec!["0".into(), "1".into()])]),
            operations: vec![
                PartialOpSignature {
                    name: "f".into(),
                    arg_sorts: vec!["V".into()],
                    out_sort: "V".into(),
                    is_total: false,
                },
                PartialOpSignature {
                    name: "g".into(),
                    arg_sorts: vec!["V".into(), "V".into()],
                    out_sort: "V".into(),
                    is_total: false,
                },
            ],
            relations: vec![],
            slots: vec![PartialSlotDecl {
                name: "xi".into(),
                sort: "V".into(),
                domain_values: vec!["0".into(), "1".into()],
            }],
            background_constraints: vec![],
            records: vec![PartialRecordSpec {
                id: "f_bot".into(),
                kind: PartialRecordKind::OpDomain {
                    op_name: "f".into(),
                    args: vec!["0".into()],
                    defined: PartialTruth::ExplicitAbsent,
                },
            }],
            max_completions: 0,
        }),
        eval_laws: vec![PartialEvalLawSpec {
            name: "g_strict".into(),
            antecedent: None,
            conclusion: PartialFormula::Eq(
                PartialTerm::App {
                    op_name: "g".into(),
                    args: vec![
                        PartialTerm::Slot("xi".into()),
                        PartialTerm::App {
                            op_name: "f".into(),
                            args: vec![PartialTerm::Const("0".into())],
                        },
                    ],
                },
                PartialTerm::Const("1".into()),
            ),
            is_required_law: false,
        }],
        quantifier_spec: None,
        open_domain: None,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    let so_p = solve_partial_task(&validate_partial_task(strict_order).unwrap())
        .partial
        .unwrap();
    assert_eq!(so_p.law_evaluations[0].strong_kleene, "false");
    assert!(so_p.kleene_soundness_verified);

    // 開領域で OpenOpTable に未登録（暗黙未定義）のタプルに対する ¬Defined(...) でも reevaluation.matched == true
    let omitted_op_open = PartialTaskSpec {
        name: "omitted_op_open_reeval".into(),
        representation: PartialRepresentation::FiniteTable(FinitePartialPresentation {
            sorts: BTreeMap::from([("V".into(), vec!["0".into()])]),
            operations: vec![],
            relations: vec![],
            slots: vec![],
            background_constraints: vec![],
            records: vec![],
            max_completions: 8,
        }),
        eval_laws: vec![],
        quantifier_spec: None,
        open_domain: Some(OpenDomainSpec {
            substructure_carriers: BTreeMap::from([("A".into(), vec!["a0".into()])]),
            ambient_carriers: BTreeMap::from([("A".into(), vec!["a0".into()])]),
            substructure_ops: vec![OpenOpTable {
                name: "f".into(),
                arg_sorts: vec!["A".into()],
                out_sort: "A".into(),
                entries: BTreeMap::new(),
            }],
            ambient_ops: vec![OpenOpTable {
                name: "f".into(),
                arg_sorts: vec!["A".into()],
                out_sort: "A".into(),
                entries: BTreeMap::new(),
            }],
            substructure_rels: vec![],
            ambient_rels: vec![],
            fiber_checks: vec![],
            positive_or_law: PartialEvalLawSpec {
                name: "not_def_f".into(),
                antecedent: None,
                conclusion: PartialFormula::Not(Box::new(PartialFormula::Defined {
                    op_name: "f".into(),
                    args: vec![PartialTerm::Const("a0".into())],
                })),
                is_required_law: false,
            },
            affine_restriction: None,
        }),
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    let omitted_od = solve_partial_task(&validate_partial_task(omitted_op_open).unwrap())
        .partial
        .unwrap()
        .open_domain
        .unwrap();
    assert_eq!(omitted_od.sub_law_eval, "true");
    assert_eq!(omitted_od.ambient_law_eval, "true");
    assert!(
        omitted_od
            .reevaluation
            .as_ref()
            .is_some_and(|r| r.checked && r.matched)
    );
}
