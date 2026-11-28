//! 第19章後半（`shigure_multisource`）計算核の単体・定理テスト。

use super::multisource::solve_multisource_task;
use crate::ir::multisource::{
    CandidateRecordSpec, MultisourceTaskSpec, SourcePresentationSpec, SupportGoalFormula,
    SupportGoalSpec, validate_multisource_task,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::revision::{RevisionConstraintSpec, RevisionCoordSpec, RevisionPredicate};
use crate::ir::term::{CoeffDomain, ScalarLit};
use std::collections::BTreeMap;

fn prov() -> Provenance {
    Provenance::new(
        vec![SourceRef::new(
            "ch19_multi_test",
            OriginKind::StaticAnalysis,
        )],
        vec![MathClause::AatCh19Thm19Dot9, MathClause::AatCh19Thm19Dot11],
    )
}

#[test]
fn ch19_theorem19_9_three_source_higher_order_conflict_and_no_overwrite() {
    // 定理 19.9 構成: 出力値域 {0, 1, 2} 上で 源 s_i は値 i を明示不在とする。
    // 任意の 2 源は整合（pairwise_consistent = true）、3 源全体 {s0, s1, s2} が唯一の極小衝突集合。
    let three_src = MultisourceTaskSpec {
        name: "thm19_9_3source".into(),
        coeff_domain: CoeffDomain::Z,
        coords: vec![RevisionCoordSpec {
            id: "y".into(),
            domain_values: vec![ScalarLit::int(0), ScalarLit::int(1), ScalarLit::int(2)],
        }],
        background_constraints: vec![],
        sources: (0..3)
            .map(|i| SourcePresentationSpec {
                source_id: format!("s{i}"),
                origin: SourceRef::new(format!("src_{i}"), OriginKind::StaticAnalysis),
                assignments: BTreeMap::new(),
                forbidden_values: vec![("y".into(), ScalarLit::int(i))],
                extra_constraints: vec![],
            })
            .collect(),
        support_goal: None,
        max_sources_subset_steps: 64,
        max_results: 32,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    let out = solve_multisource_task(&validate_multisource_task(three_src).unwrap());
    assert_eq!(out.verdict, Verdict::Refuted);
    let ms = out.multisource.unwrap();
    assert!(ms.pairwise_consistent);
    assert!(!ms.all_sources_consistent);
    assert!(ms.minimal_conflicts_verified);
    assert_eq!(
        ms.minimal_conflict_sets,
        vec![vec!["s0".to_owned(), "s1".to_owned(), "s2".to_owned()]]
    );

    // 上書きせず両方課す: s0 が y=0、s1 が y=1 なら 2 源極小衝突（pairwise_consistent=false）
    let direct_clash = MultisourceTaskSpec {
        name: "direct_no_overwrite".into(),
        coeff_domain: CoeffDomain::Z,
        coords: vec![RevisionCoordSpec {
            id: "y".into(),
            domain_values: vec![ScalarLit::int(0), ScalarLit::int(1)],
        }],
        background_constraints: vec![],
        sources: vec![
            SourcePresentationSpec {
                source_id: "s0".into(),
                origin: SourceRef::new("src_a", OriginKind::RuntimeObservation),
                assignments: BTreeMap::from([("y".into(), ScalarLit::int(0))]),
                forbidden_values: vec![],
                extra_constraints: vec![],
            },
            SourcePresentationSpec {
                source_id: "s1".into(),
                origin: SourceRef::new("src_b", OriginKind::HumanAdopted),
                assignments: BTreeMap::from([("y".into(), ScalarLit::int(1))]),
                forbidden_values: vec![],
                extra_constraints: vec![],
            },
        ],
        support_goal: None,
        max_sources_subset_steps: 64,
        max_results: 32,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    let clash_out = solve_multisource_task(&validate_multisource_task(direct_clash).unwrap());
    assert_eq!(clash_out.verdict, Verdict::Refuted);
    let cm = clash_out.multisource.unwrap();
    assert!(!cm.pairwise_consistent);
    assert_eq!(
        cm.minimal_conflict_sets,
        vec![vec!["s0".to_owned(), "s1".to_owned()]]
    );
}

#[test]
fn ch19_example19_13_two_minimal_supports_cost_stability_and_prop19_12() {
    // 例 19.13: 構造制約 omega = xi - eta（LinearZero: omega - xi + eta = 0）
    // 候補 h_w (omega=0, cost=3), h_x (xi=0, cost=1), h_e (eta=0, cost=1)
    // 目標: xi == eta。極小由来支持は {h_w} (費用 3) と {h_x, h_e} (費用 2) の 2 通り。
    let ex13 = MultisourceTaskSpec {
        name: "ex_19_13_support".into(),
        coeff_domain: CoeffDomain::Z,
        coords: vec![
            RevisionCoordSpec {
                id: "xi".into(),
                domain_values: vec![ScalarLit::int(0), ScalarLit::int(1)],
            },
            RevisionCoordSpec {
                id: "eta".into(),
                domain_values: vec![ScalarLit::int(0), ScalarLit::int(1)],
            },
            RevisionCoordSpec {
                id: "omega".into(),
                domain_values: vec![ScalarLit::int(-1), ScalarLit::int(0), ScalarLit::int(1)],
            },
        ],
        background_constraints: vec![RevisionConstraintSpec {
            id: "diff_eq".into(),
            support: vec!["omega".into(), "xi".into(), "eta".into()],
            predicate: RevisionPredicate::LinearZero {
                terms: vec![
                    (ScalarLit::int(1), "omega".into()),
                    (ScalarLit::int(-1), "xi".into()),
                    (ScalarLit::int(1), "eta".into()),
                ],
            },
        }],
        sources: vec![],
        support_goal: Some(SupportGoalSpec {
            trusted_assignments: BTreeMap::new(),
            candidates: vec![
                CandidateRecordSpec {
                    id: "h_w".into(),
                    coord: "omega".into(),
                    value: ScalarLit::int(0),
                    cost: Some(ScalarLit::int(3)),
                    origin: SourceRef::new("cand_w", OriginKind::LlmCandidate),
                    verified_actual_value: None,
                },
                CandidateRecordSpec {
                    id: "h_x".into(),
                    coord: "xi".into(),
                    value: ScalarLit::int(0),
                    cost: Some(ScalarLit::int(1)),
                    origin: SourceRef::new("cand_x", OriginKind::LlmCandidate),
                    verified_actual_value: None,
                },
                CandidateRecordSpec {
                    id: "h_e".into(),
                    coord: "eta".into(),
                    value: ScalarLit::int(0),
                    cost: Some(ScalarLit::int(1)),
                    origin: SourceRef::new("cand_e", OriginKind::LlmCandidate),
                    verified_actual_value: None,
                },
            ],
            goal: SupportGoalFormula::CoordEquality("xi".into(), "eta".into()),
            expected_truth: true,
            check_post_adoption_stability: true,
        }),
        max_sources_subset_steps: 256,
        max_results: 32,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };

    let out = solve_multisource_task(&validate_multisource_task(ex13.clone()).unwrap());
    assert_eq!(out.verdict, Verdict::Established);
    let sg = out.multisource.unwrap().support_goal.unwrap();
    assert!(sg.all_candidates_consistent);
    assert_eq!(sg.minimal_supports.len(), 2);
    assert!(sg.minimal_supports.iter().all(|e| e.stability_verified));
    assert_eq!(sg.min_cost_supports.len(), 1);
    assert_eq!(
        sg.min_cost_supports[0].support,
        vec!["h_e".to_owned(), "h_x".to_owned()]
    );
    assert_eq!(sg.min_cost_supports[0].total_cost.as_deref(), Some("2"));
    assert!(
        sg.reevaluation
            .as_ref()
            .is_some_and(|r| r.checked && r.matched)
    );

    // 命題 19.12: h_w の実測値が 1 (omega=1 => xi=eta は不成立) だった場合、改訂再評価が走る
    let mut mismatch = ex13.clone();
    let sg_m = mismatch.support_goal.as_mut().unwrap();
    sg_m.candidates[0].verified_actual_value = Some(ScalarLit::int(1));
    let out_mis = solve_multisource_task(&validate_multisource_task(mismatch).unwrap());
    assert_eq!(out_mis.verdict, Verdict::Established);
    let sg_rev = out_mis.multisource.unwrap().support_goal.unwrap();
    assert!(sg_rev.post_verification_reeval_needed);
    let pv = sg_rev.post_verification_minimal_supports.unwrap();
    // omega=1 のもと xi==eta にできる整合支持は空（{h_x, h_e} も矛盾するため空補完排除）
    assert!(pv.is_empty());

    // 非整合候補族: 極小横断集合として不整合な {c0, c1} と整合な {c2} の両方が列挙され、
    // 空補完になる {c0, c1} を非空性検査で除外し Comp(T_S) != empty の {c2} のみ残す
    let inconsistent_cands = MultisourceTaskSpec {
        name: "inconsistent_cands_filter".into(),
        coeff_domain: CoeffDomain::Z,
        coords: vec![
            RevisionCoordSpec {
                id: "x".into(),
                domain_values: vec![ScalarLit::int(0), ScalarLit::int(1)],
            },
            RevisionCoordSpec {
                id: "y".into(),
                domain_values: vec![ScalarLit::int(0), ScalarLit::int(1)],
            },
        ],
        background_constraints: vec![],
        sources: vec![],
        support_goal: Some(SupportGoalSpec {
            trusted_assignments: BTreeMap::new(),
            candidates: vec![
                CandidateRecordSpec {
                    id: "c0".into(),
                    coord: "x".into(),
                    value: ScalarLit::int(0),
                    cost: None,
                    origin: SourceRef::new("c0", OriginKind::LlmCandidate),
                    verified_actual_value: None,
                },
                CandidateRecordSpec {
                    id: "c1".into(),
                    coord: "x".into(),
                    value: ScalarLit::int(1),
                    cost: None,
                    origin: SourceRef::new("c1", OriginKind::LlmCandidate),
                    verified_actual_value: None,
                },
                CandidateRecordSpec {
                    id: "c2".into(),
                    coord: "y".into(),
                    value: ScalarLit::int(0),
                    cost: None,
                    origin: SourceRef::new("c2", OriginKind::LlmCandidate),
                    verified_actual_value: None,
                },
            ],
            goal: SupportGoalFormula::CoordEqualsConst("y".into(), ScalarLit::int(0)),
            expected_truth: true,
            check_post_adoption_stability: true,
        }),
        max_sources_subset_steps: 256,
        max_results: 32,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    let inc_out = solve_multisource_task(&validate_multisource_task(inconsistent_cands).unwrap());
    assert_eq!(inc_out.verdict, Verdict::Established);
    let inc_sg = inc_out.multisource.unwrap().support_goal.unwrap();
    assert!(!inc_sg.all_candidates_consistent);
    assert_eq!(inc_sg.minimal_supports.len(), 1);
    assert_eq!(inc_sg.minimal_supports[0].support, vec!["c2".to_owned()]);

    // 多数の単独不整合源（m = 30: 25 個が単独不整合、5 個が整合）が超集合枝刈りで即座に完了すること
    let mut many_singletons = Vec::new();
    for i in 0..30usize {
        let assignments = if i < 25 {
            BTreeMap::from([("y".into(), ScalarLit::int(99))])
        } else {
            BTreeMap::from([("y".into(), ScalarLit::int(0))])
        };
        many_singletons.push(SourcePresentationSpec {
            source_id: format!("ms_{i:02}"),
            origin: SourceRef::new(format!("src_{i}"), OriginKind::StaticAnalysis),
            assignments,
            forbidden_values: vec![],
            extra_constraints: vec![],
        });
    }
    let pruned_30 = MultisourceTaskSpec {
        name: "pruned_30_singletons".into(),
        coeff_domain: CoeffDomain::Z,
        coords: vec![RevisionCoordSpec {
            id: "y".into(),
            domain_values: vec![ScalarLit::int(0), ScalarLit::int(1)],
        }],
        background_constraints: vec![],
        sources: many_singletons,
        support_goal: None,
        max_sources_subset_steps: 50_000,
        max_results: 64,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    let p30_out = solve_multisource_task(&validate_multisource_task(pruned_30).unwrap());
    assert_eq!(p30_out.verdict, Verdict::Refuted);
    let p30_ms = p30_out.multisource.unwrap();
    assert!(p30_ms.minimal_conflicts_verified);
    assert_eq!(p30_ms.minimal_conflict_sets.len(), 25);

    // 不足反例: 全候補を入れても目標と逆になる補完が残る場合 insufficiency_witness を返す
    let mut insufficient = ex13;
    insufficient
        .support_goal
        .as_mut()
        .unwrap()
        .candidates
        .retain(|c| c.id == "h_x");
    let ins_out = solve_multisource_task(&validate_multisource_task(insufficient).unwrap());
    assert_eq!(ins_out.verdict, Verdict::Refuted);
    let ins_sg = ins_out.multisource.unwrap().support_goal.unwrap();
    assert!(ins_sg.minimal_supports.is_empty());
    assert!(ins_sg.insufficiency_witness.is_some());

    // 上限超過で FiniteEnumerationOutOfScope
    let bounded = MultisourceTaskSpec {
        name: "bounded_sources".into(),
        coeff_domain: CoeffDomain::Z,
        coords: vec![RevisionCoordSpec {
            id: "y".into(),
            domain_values: vec![ScalarLit::int(0)],
        }],
        background_constraints: vec![],
        sources: (0..3)
            .map(|i| SourcePresentationSpec {
                source_id: format!("s{i}"),
                origin: SourceRef::new(format!("b_{i}"), OriginKind::StaticAnalysis),
                assignments: BTreeMap::new(),
                forbidden_values: vec![],
                extra_constraints: vec![],
            })
            .collect(),
        support_goal: None,
        max_sources_subset_steps: 2,
        max_results: 32,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    assert!(matches!(
        solve_multisource_task(&validate_multisource_task(bounded).unwrap()).verdict,
        Verdict::Undetermined(SilenceReason::FiniteEnumerationOutOfScope { .. })
    ));
}
