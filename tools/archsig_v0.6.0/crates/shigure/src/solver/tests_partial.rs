//! 第18章（`shigure_partial`）計算核の単体・定理・パラメトリックテスト。

use super::partial_eval::solve_partial_task;
use crate::ir::partial::{
    AffinePartialPresentation, AffineRestrictionSpec, FiberCoverageCheckSpec,
    FinitePartialPresentation, OpenDomainSpec, OpenOpTable, OpenRelTable, PartialArithOp,
    PartialEvalLawSpec, PartialFormula, PartialOpSignature, PartialPredSignature,
    PartialRecordKind, PartialRecordSpec, PartialRepresentation, PartialSlotDecl, PartialTaskSpec,
    PartialTerm, PartialTruth, PartialValue, QuantifierCompletionSpec, QuantifierHierarchySpec,
    validate_partial_task,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::term::{CoeffDomain, ScalarLit};
use std::collections::{BTreeMap, BTreeSet};

fn prov() -> Provenance {
    Provenance::new(
        vec![SourceRef::new("ch18_test", OriginKind::StaticAnalysis)],
        vec![MathClause::AatCh18Thm18Dot3],
    )
}

#[test]
fn ch18_example18_2_finite_mus_and_no_eval_law_mixing() {
    // 例 18.2: 記録 r1 (xi=0), r2 (xi=1), r3 (c=0) において、r1 と r2 が唯一の MUS を作る。
    // また整合版で is_required_law=true の評価 Law (c=1) を与えても Comp(T_S) の数え上げ自体には混入しない。
    let inconsistent = PartialTaskSpec {
        name: "ex_18_2_inconsistent".into(),
        representation: PartialRepresentation::FiniteTable(FinitePartialPresentation {
            sorts: BTreeMap::from([("V".into(), vec!["0".into(), "1".into()])]),
            operations: vec![],
            relations: vec![],
            slots: vec![
                PartialSlotDecl {
                    name: "xi".into(),
                    sort: "V".into(),
                    domain_values: vec!["0".into(), "1".into()],
                },
                PartialSlotDecl {
                    name: "eta".into(),
                    sort: "V".into(),
                    domain_values: vec!["0".into(), "1".into()],
                },
            ],
            background_constraints: vec![],
            records: vec![
                PartialRecordSpec {
                    id: "r1".into(),
                    kind: PartialRecordKind::SlotAssignment {
                        slot: "xi".into(),
                        value: "0".into(),
                    },
                },
                PartialRecordSpec {
                    id: "r2".into(),
                    kind: PartialRecordKind::SlotAssignment {
                        slot: "xi".into(),
                        value: "1".into(),
                    },
                },
                PartialRecordSpec {
                    id: "r3".into(),
                    kind: PartialRecordKind::SlotAssignment {
                        slot: "eta".into(),
                        value: "0".into(),
                    },
                },
            ],
            max_completions: 64,
        }),
        eval_laws: vec![],
        quantifier_spec: None,
        open_domain: None,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    let out_inc = solve_partial_task(&validate_partial_task(inconsistent).unwrap());
    assert_eq!(out_inc.verdict, Verdict::Refuted);
    let p_inc = out_inc.partial.unwrap();
    assert!(!p_inc.completion_consistent);
    assert!(p_inc.mus_verified);
    assert_eq!(
        p_inc.minimal_inconsistent_subsets,
        vec![vec!["r1".to_owned(), "r2".to_owned()]]
    );

    // 整合表現上で反例となる評価 Law を置いても、Comp(T_S) = 2 は維持され、Law は supervaluation=false と判定される。
    let consistent_with_false_law = PartialTaskSpec {
        name: "ex_18_2_no_mixing".into(),
        representation: PartialRepresentation::FiniteTable(FinitePartialPresentation {
            sorts: BTreeMap::from([("V".into(), vec!["0".into(), "1".into()])]),
            operations: vec![],
            relations: vec![],
            slots: vec![
                PartialSlotDecl {
                    name: "xi".into(),
                    sort: "V".into(),
                    domain_values: vec!["0".into(), "1".into()],
                },
                PartialSlotDecl {
                    name: "eta".into(),
                    sort: "V".into(),
                    domain_values: vec!["0".into(), "1".into()],
                },
            ],
            background_constraints: vec![],
            records: vec![PartialRecordSpec {
                id: "r1".into(),
                kind: PartialRecordKind::SlotAssignment {
                    slot: "xi".into(),
                    value: "0".into(),
                },
            }],
            max_completions: 64,
        }),
        eval_laws: vec![PartialEvalLawSpec {
            name: "req_law".into(),
            antecedent: None,
            conclusion: PartialFormula::Eq(
                PartialTerm::Slot("xi".into()),
                PartialTerm::Const("1".into()),
            ),
            is_required_law: true,
        }],
        quantifier_spec: None,
        open_domain: None,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    let out_no_mix = solve_partial_task(&validate_partial_task(consistent_with_false_law).unwrap());
    assert_eq!(out_no_mix.verdict, Verdict::Refuted);
    let p_nomix = out_no_mix.partial.unwrap();
    assert!(p_nomix.completion_consistent);
    assert_eq!(p_nomix.completion_count, Some(2));
    assert_eq!(p_nomix.law_evaluations[0].supervaluation, "false");
    assert_eq!(p_nomix.law_evaluations[0].strong_kleene, "false");
    assert!(p_nomix.kleene_soundness_verified);
}

#[test]
fn ch18_strong_kleene_strict_let_and_example18_7_correlations() {
    // 正格 `let` 評価と例 18.7 の 3 種相関（正相関・負相関・混在）
    let spec = PartialTaskSpec {
        name: "kleene_and_ex18_7".into(),
        representation: PartialRepresentation::FiniteTable(FinitePartialPresentation {
            sorts: BTreeMap::from([("V".into(), vec!["0".into(), "1".into()])]),
            operations: vec![PartialOpSignature {
                name: "f".into(),
                arg_sorts: vec!["V".into()],
                out_sort: "V".into(),
                is_total: false,
            }],
            relations: vec![],
            slots: vec![
                PartialSlotDecl {
                    name: "a".into(),
                    sort: "V".into(),
                    domain_values: vec!["0".into(), "1".into()],
                },
                PartialSlotDecl {
                    name: "b".into(),
                    sort: "V".into(),
                    domain_values: vec!["0".into(), "1".into()],
                },
            ],
            background_constraints: vec![],
            records: vec![
                PartialRecordSpec {
                    id: "f0".into(),
                    kind: PartialRecordKind::OpValue {
                        op_name: "f".into(),
                        args: vec!["0".into()],
                        value: PartialValue::ExplicitAbsent,
                    },
                },
                PartialRecordSpec {
                    id: "f1".into(),
                    kind: PartialRecordKind::OpValue {
                        op_name: "f".into(),
                        args: vec!["1".into()],
                        value: PartialValue::Known("1".into()),
                    },
                },
                // 背景では a = b または b 独立を調べるため、a=0 -> slot_a, b -> 未指定にする代わりに 18.7 相関を直接組む:
                // ここでは a と b に OpValue(UnobservedSlot) を持たせる代わりに Slot 間で相関を持たせず、
                // まず strict let と OR 排中律 (supervaluation true vs Kleene unknown) を検証する。
            ],
            max_completions: 64,
        }),
        eval_laws: vec![
            // 正格 let: f(0) が明示不在のため、本体が定数でも全体は成立しない (false)
            PartialEvalLawSpec {
                name: "strict_let_bot".into(),
                antecedent: None,
                conclusion: PartialFormula::Eq(
                    PartialTerm::Let {
                        var: "x".into(),
                        bound: Box::new(PartialTerm::App {
                            op_name: "f".into(),
                            args: vec![PartialTerm::Const("0".into())],
                        }),
                        body: Box::new(PartialTerm::Const("1".into())),
                    },
                    PartialTerm::Const("1".into()),
                ),
                is_required_law: false,
            },
            // 排中律: a=0 \/ a=1 は Kleene では unknown だが Supervaluation では true（健全）
            PartialEvalLawSpec {
                name: "tautology".into(),
                antecedent: None,
                conclusion: PartialFormula::Or(vec![
                    PartialFormula::Eq(
                        PartialTerm::Slot("a".into()),
                        PartialTerm::Const("0".into()),
                    ),
                    PartialFormula::Eq(
                        PartialTerm::Slot("a".into()),
                        PartialTerm::Const("1".into()),
                    ),
                ]),
                is_required_law: false,
            },
            // a + 0 == a は算術 BinOp 評価で検証
            PartialEvalLawSpec {
                name: "arith_plus_zero".into(),
                antecedent: None,
                conclusion: PartialFormula::Eq(
                    PartialTerm::BinOp {
                        op: PartialArithOp::Add,
                        lhs: Box::new(PartialTerm::Const("1".into())),
                        rhs: Box::new(PartialTerm::Const("0".into())),
                    },
                    PartialTerm::Const("1".into()),
                ),
                is_required_law: false,
            },
        ],
        quantifier_spec: None,
        open_domain: None,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    let out = solve_partial_task(&validate_partial_task(spec).unwrap());
    assert_eq!(out.verdict, Verdict::Established);
    let p = out.partial.unwrap();
    assert!(p.kleene_soundness_verified);
    assert_eq!(p.law_evaluations[0].strong_kleene, "false");
    assert_eq!(p.law_evaluations[0].supervaluation, "false");
    assert_eq!(p.law_evaluations[1].strong_kleene, "unknown");
    assert_eq!(p.law_evaluations[1].supervaluation, "true");
    assert_eq!(p.law_evaluations[2].strong_kleene, "true");
    assert_eq!(p.law_evaluations[2].supervaluation, "true");

    // 例 18.7 の 3 相関: 背景 SlotEquality(xi, eta) のもとで
    // 1) (xi=0 |- eta=0) => 前提成立時に必ず成立 (valid_on_antecedent_domain)
    // 2) (xi=0 |- eta=1) => 前提成立時に必ず反証 (refuted_on_antecedent_domain)
    // 3) (xi=0 |- zeta=0) => 独立スロット zeta により混在 (indeterminate_on_antecedent_domain)
    let corr_spec = PartialTaskSpec {
        name: "ex_18_7_correlations".into(),
        representation: PartialRepresentation::FiniteTable(FinitePartialPresentation {
            sorts: BTreeMap::from([("V".into(), vec!["0".into(), "1".into()])]),
            operations: vec![],
            relations: vec![],
            slots: vec![
                PartialSlotDecl {
                    name: "xi".into(),
                    sort: "V".into(),
                    domain_values: vec!["0".into(), "1".into()],
                },
                PartialSlotDecl {
                    name: "eta".into(),
                    sort: "V".into(),
                    domain_values: vec!["0".into(), "1".into()],
                },
                PartialSlotDecl {
                    name: "zeta".into(),
                    sort: "V".into(),
                    domain_values: vec!["0".into(), "1".into()],
                },
            ],
            background_constraints: vec![crate::ir::partial::BackgroundConstraint::SlotEquality(
                "xi".into(),
                "eta".into(),
            )],
            records: vec![],
            max_completions: 64,
        }),
        eval_laws: vec![
            PartialEvalLawSpec {
                name: "same_sign".into(),
                antecedent: Some(PartialFormula::Eq(
                    PartialTerm::Slot("xi".into()),
                    PartialTerm::Const("0".into()),
                )),
                conclusion: PartialFormula::Eq(
                    PartialTerm::Slot("eta".into()),
                    PartialTerm::Const("0".into()),
                ),
                is_required_law: false,
            },
            PartialEvalLawSpec {
                name: "anti_correlated".into(),
                antecedent: Some(PartialFormula::Eq(
                    PartialTerm::Slot("xi".into()),
                    PartialTerm::Const("0".into()),
                )),
                conclusion: PartialFormula::Eq(
                    PartialTerm::Slot("eta".into()),
                    PartialTerm::Const("1".into()),
                ),
                is_required_law: false,
            },
            PartialEvalLawSpec {
                name: "independent_mixed".into(),
                antecedent: Some(PartialFormula::Eq(
                    PartialTerm::Slot("xi".into()),
                    PartialTerm::Const("0".into()),
                )),
                conclusion: PartialFormula::Eq(
                    PartialTerm::Slot("zeta".into()),
                    PartialTerm::Const("0".into()),
                ),
                is_required_law: false,
            },
        ],
        quantifier_spec: None,
        open_domain: None,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    let corr_out = solve_partial_task(&validate_partial_task(corr_spec).unwrap());
    let cp = corr_out.partial.unwrap();
    assert_eq!(cp.completion_count, Some(4));
    assert_eq!(
        cp.law_evaluations[0].conditional_conclusion_eval.as_deref(),
        Some("valid_on_antecedent_domain")
    );
    assert_eq!(
        cp.law_evaluations[1].conditional_conclusion_eval.as_deref(),
        Some("refuted_on_antecedent_domain")
    );
    assert_eq!(
        cp.law_evaluations[2].conditional_conclusion_eval.as_deref(),
        Some("indeterminate_on_antecedent_domain")
    );
}

#[test]
fn ch18_affine_partial_prop18_9_and_inconsistent_mus_over_q_and_z() {
    // 命題 18.9: x = (x0 + t, x1 + t) （自由パラメータ t）, 評価方程式 x0 - x1 = 0 は 0 = 0 に正規化され真。
    // 一方 x0 = 1 はパラメータ依存のまま indeterminate。
    let aff_q = PartialTaskSpec {
        name: "affine_prop_18_9".into(),
        representation: PartialRepresentation::Affine(AffinePartialPresentation {
            coeff_domain: CoeffDomain::Q,
            coord_names: vec!["x".into(), "y".into()],
            x0: vec![ScalarLit::rat(0, 1).unwrap(), ScalarLit::rat(0, 1).unwrap()],
            direction_t: vec![
                vec![ScalarLit::rat(1, 1).unwrap()],
                vec![ScalarLit::rat(1, 1).unwrap()],
            ],
            background_rows: vec![],
            record_rows: vec![],
            eval_equations: vec![
                (
                    "invariant_diff".into(),
                    vec![
                        ScalarLit::rat(1, 1).unwrap(),
                        ScalarLit::rat(-1, 1).unwrap(),
                    ],
                    ScalarLit::rat(0, 1).unwrap(),
                ),
                (
                    "dependent_x".into(),
                    vec![ScalarLit::rat(1, 1).unwrap(), ScalarLit::rat(0, 1).unwrap()],
                    ScalarLit::rat(1, 1).unwrap(),
                ),
            ],
        }),
        eval_laws: vec![],
        quantifier_spec: None,
        open_domain: None,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    let out_q = solve_partial_task(&validate_partial_task(aff_q).unwrap());
    assert_eq!(out_q.verdict, Verdict::Established);
    let pq = out_q.partial.unwrap();
    assert_eq!(pq.law_evaluations[0].supervaluation, "true");
    assert_eq!(
        pq.law_evaluations[0].affine_normalized_eval.as_deref(),
        Some("0 = 0 (always_true)")
    );
    assert_eq!(pq.law_evaluations[1].supervaluation, "indeterminate");

    // Z 上の 2p = 1 不整合と MUS 抽出・検算
    let aff_z_bad = PartialTaskSpec {
        name: "affine_z_mus".into(),
        representation: PartialRepresentation::Affine(AffinePartialPresentation {
            coeff_domain: CoeffDomain::Z,
            coord_names: vec!["p".into()],
            x0: vec![ScalarLit::int(0)],
            direction_t: vec![vec![]],
            background_rows: vec![],
            record_rows: vec![
                (
                    "even_two".into(),
                    vec![ScalarLit::int(2)],
                    ScalarLit::int(1),
                ),
                ("aux_ok".into(), vec![ScalarLit::int(1)], ScalarLit::int(0)),
            ],
            eval_equations: vec![],
        }),
        eval_laws: vec![],
        quantifier_spec: None,
        open_domain: None,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    let out_z = solve_partial_task(&validate_partial_task(aff_z_bad).unwrap());
    assert_eq!(out_z.verdict, Verdict::Refuted);
    let pz = out_z.partial.unwrap();
    assert!(!pz.completion_consistent);
    assert!(pz.mus_verified);
    assert_eq!(pz.minimal_inconsistent_subsets, vec![vec!["even_two"]]);
}

#[test]
fn ch18_quantifier_4_levels_and_theorem18_12_hitting_sets() {
    let run_q = |completions: Vec<QuantifierCompletionSpec>| {
        let spec = PartialTaskSpec {
            name: "q_test".into(),
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
            quantifier_spec: Some(QuantifierHierarchySpec {
                candidates: vec!["x1".into(), "x2".into()],
                completions,
                max_steps: 1024,
            }),
            open_domain: None,
            provenance: prov(),
            undeclared_unobserved_slots: vec![],
        };
        solve_partial_task(&validate_partial_task(spec).unwrap())
            .partial
            .unwrap()
            .quantifier_hierarchy
            .unwrap()
    };

    // 1. E=true, U=true, Q=false, G=false（各補完に一意解があるが共通解なし；slot s1 が必要スロット）
    let q_u_no_q = run_q(vec![
        QuantifierCompletionSpec {
            id: "c1".into(),
            slot_values: BTreeMap::from([("s1".into(), "0".into()), ("s2".into(), "0".into())]),
            valid_candidates: vec!["x1".into()],
            output_value: "a".into(),
        },
        QuantifierCompletionSpec {
            id: "c2".into(),
            slot_values: BTreeMap::from([("s1".into(), "1".into()), ("s2".into(), "0".into())]),
            valid_candidates: vec!["x2".into()],
            output_value: "b".into(),
        },
    ]);
    assert!(q_u_no_q.e_holds && q_u_no_q.u_holds && !q_u_no_q.q_holds && !q_u_no_q.g_holds);
    assert!(q_u_no_q.g_iff_u_and_q_verified);
    assert_eq!(q_u_no_q.required_slot_sets, vec![vec!["s1".to_owned()]]);

    // 2. E=true, U=false, Q=true, G=false（共通解は唯一 x1 だが c1 で一意性を欠く）
    let q_q_no_u = run_q(vec![
        QuantifierCompletionSpec {
            id: "c1".into(),
            slot_values: BTreeMap::from([("s1".into(), "0".into())]),
            valid_candidates: vec!["x1".into(), "x2".into()],
            output_value: "a".into(),
        },
        QuantifierCompletionSpec {
            id: "c2".into(),
            slot_values: BTreeMap::from([("s1".into(), "1".into())]),
            valid_candidates: vec!["x1".into()],
            output_value: "b".into(),
        },
    ]);
    assert!(q_q_no_u.e_holds && !q_q_no_u.u_holds && q_q_no_u.q_holds && !q_q_no_u.g_holds);
    assert!(q_q_no_u.g_iff_u_and_q_verified);
    assert_eq!(q_q_no_u.required_slot_sets, vec![vec!["s1".to_owned()]]);

    // 3. E=true, U=false, Q=false, G=false（両方複数有効解で一意共通解もなし）
    let q_e_only = run_q(vec![
        QuantifierCompletionSpec {
            id: "c1".into(),
            slot_values: BTreeMap::from([("s1".into(), "0".into())]),
            valid_candidates: vec!["x1".into(), "x2".into()],
            output_value: "ok".into(),
        },
        QuantifierCompletionSpec {
            id: "c2".into(),
            slot_values: BTreeMap::from([("s1".into(), "1".into())]),
            valid_candidates: vec!["x1".into(), "x2".into()],
            output_value: "ok".into(),
        },
    ]);
    assert!(q_e_only.e_holds && !q_e_only.u_holds && !q_e_only.q_holds && !q_e_only.g_holds);
    assert!(q_e_only.g_iff_u_and_q_verified);

    // 4. E=true, U=true, Q=true, G=true（共通の唯一解 x1）
    let q_all = run_q(vec![
        QuantifierCompletionSpec {
            id: "c1".into(),
            slot_values: BTreeMap::from([("s1".into(), "0".into())]),
            valid_candidates: vec!["x1".into()],
            output_value: "ok".into(),
        },
        QuantifierCompletionSpec {
            id: "c2".into(),
            slot_values: BTreeMap::from([("s1".into(), "1".into())]),
            valid_candidates: vec!["x1".into()],
            output_value: "ok".into(),
        },
    ]);
    assert!(q_all.e_holds && q_all.u_holds && q_all.q_holds && q_all.g_holds);
    assert!(q_all.g_iff_u_and_q_verified);

    // 5. E=false かつ同一スロットで可解性が割れる不足反例（insufficiency_witness）
    let q_not_e = run_q(vec![
        QuantifierCompletionSpec {
            id: "c1".into(),
            slot_values: BTreeMap::from([("s1".into(), "0".into())]),
            valid_candidates: vec!["x1".into()],
            output_value: "a".into(),
        },
        QuantifierCompletionSpec {
            id: "c2".into(),
            slot_values: BTreeMap::from([("s1".into(), "0".into())]),
            valid_candidates: vec![],
            output_value: "a".into(),
        },
    ]);
    assert!(!q_not_e.e_holds && !q_not_e.u_holds && !q_not_e.q_holds && !q_not_e.g_holds);
    assert!(q_not_e.g_iff_u_and_q_verified);
    assert!(q_not_e.required_slot_sets.is_empty());
    assert!(q_not_e.insufficiency_witness.is_some());

    // 6. 空の補完族は定義 18.10 の前提外として Undetermined
    let empty_q = PartialTaskSpec {
        name: "q_empty".into(),
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
        quantifier_spec: Some(QuantifierHierarchySpec {
            candidates: vec!["x1".into()],
            completions: vec![],
            max_steps: 1024,
        }),
        open_domain: None,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    assert!(matches!(
        solve_partial_task(&validate_partial_task(empty_q).unwrap()).verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { .. })
    ));
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
}
