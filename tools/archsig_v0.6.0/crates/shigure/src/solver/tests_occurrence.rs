//! 第17章（`shigure_occurrence`）計算核の単体・定理・パラメトリックテスト。

use super::occurrence::solve_occurrence_task;
use crate::algebra::congruence::{OpOutputRecord, PredicateRecord, PredicateRecordKind};
use crate::ir::occurrence::{
    OccurrenceInitialReadoutSpec, OccurrenceOpSpec, OccurrenceReadingSpec, OccurrenceRelSpec,
    OccurrenceSortSpec, OccurrenceTaskSpec, validate_occurrence_task,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use std::collections::{BTreeMap, BTreeSet};

fn prov() -> Provenance {
    Provenance::new(
        vec![SourceRef::new("ch17_test", OriginKind::StaticAnalysis)],
        vec![MathClause::AatCh17Thm17Dot2],
    )
}

#[test]
fn ch17_def17_1_and_thm17_2_detect_implicit_domain_collision_with_verified_derivation() {
    let spec = OccurrenceTaskSpec {
        name: "def17_1_collision".into(),
        sorts: vec![
            OccurrenceSortSpec {
                name: "S".into(),
                elements: vec!["a".into(), "b".into()],
                is_fixed_value: false,
            },
            OccurrenceSortSpec {
                name: "V".into(),
                elements: vec!["0".into(), "1".into()],
                is_fixed_value: true,
            },
        ],
        operations: vec![OccurrenceOpSpec {
            name: "f".into(),
            arg_sorts: vec!["S".into()],
            out_sort: "V".into(),
            is_total: false,
        }],
        relations: vec![],
        identity_requests: vec![("S".into(), "a".into(), "b".into())],
        op_records: vec![OpOutputRecord {
            op_name: "f".into(),
            arg_sorts: vec!["S".into()],
            args: vec!["a".into()],
            out_sort: "V".into(),
            output: "0".into(),
            positive: true,
        }],
        // G_f^+(a, 0) から D_f^+(a) が補完され、D_f^-(b) との衝突が検出・検算される。
        pred_records: vec![PredicateRecord {
            kind: PredicateRecordKind::Domain,
            name: "f".into(),
            arg_sorts: vec!["S".into()],
            args: vec!["b".into()],
            positive: false,
        }],
        base_readings: vec![],
        context_closed_17_5: false,
        explicit_contexts: vec![],
        preserve_full_domains: vec![],
        initial_readouts: vec![],
        provenance: prov(),
        max_congruence_steps: 0,
        max_partitions: 0,
        undeclared_unobserved_slots: vec![],
    };
    let task = validate_occurrence_task(spec).unwrap();
    let out = solve_occurrence_task(&task);
    assert_eq!(out.verdict, Verdict::Refuted);
    let occ = out.occurrence.expect("occurrence detail");
    assert!(occ.derivation_verified);
    assert!(
        occ.collisions
            .iter()
            .any(|c| c.kind == "domain_record_collision")
    );
}

#[test]
fn ch17_setting17_5_context_refinement_and_incomplete_table_silence() {
    let closed = OccurrenceTaskSpec {
        name: "setting_17_5_ok".into(),
        sorts: vec![
            OccurrenceSortSpec {
                name: "S".into(),
                elements: vec!["a".into(), "b".into(), "c".into()],
                is_fixed_value: false,
            },
            OccurrenceSortSpec {
                name: "V".into(),
                elements: vec!["0".into(), "1".into()],
                is_fixed_value: true,
            },
        ],
        operations: vec![OccurrenceOpSpec {
            name: "T".into(),
            arg_sorts: vec!["S".into()],
            out_sort: "S".into(),
            is_total: true,
        }],
        relations: vec![],
        identity_requests: vec![],
        op_records: vec![
            OpOutputRecord {
                op_name: "T".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["a".into()],
                out_sort: "S".into(),
                output: "c".into(),
                positive: true,
            },
            OpOutputRecord {
                op_name: "T".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["b".into()],
                out_sort: "S".into(),
                output: "c".into(),
                positive: true,
            },
            OpOutputRecord {
                op_name: "T".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["c".into()],
                out_sort: "S".into(),
                output: "a".into(),
                positive: true,
            },
        ],
        pred_records: vec![],
        base_readings: vec![OccurrenceReadingSpec {
            name: "obs".into(),
            sort: "S".into(),
            values: BTreeMap::from([
                ("a".into(), Some("0".into())),
                ("b".into(), Some("0".into())),
                ("c".into(), Some("1".into())),
            ]),
        }],
        context_closed_17_5: true,
        explicit_contexts: vec![],
        preserve_full_domains: vec![],
        initial_readouts: vec![],
        provenance: prov(),
        max_congruence_steps: 0,
        max_partitions: 0,
        undeclared_unobserved_slots: vec![],
    };
    let out = solve_occurrence_task(&validate_occurrence_task(closed.clone()).unwrap());
    assert_eq!(out.verdict, Verdict::Established);
    let occ = out.occurrence.unwrap();
    assert!(occ.coarsest_sound_exists);
    let cls = occ.coarsest_sound_classes.unwrap();
    assert_eq!(cls["S"], vec![vec!["a", "b"], vec!["c"]]);

    // 未完全定義表は設定 17.5 未充足で理由付き undetermined になる
    let mut incomplete = closed;
    incomplete.op_records.pop();
    let out_inc = solve_occurrence_task(&validate_occurrence_task(incomplete).unwrap());
    assert!(matches!(
        out_inc.verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { .. })
    ));
}

#[test]
fn ch17_example17_7_partial_recording_has_no_coarsest_sound_quotient() {
    let spec = OccurrenceTaskSpec {
        name: "ex_17_7".into(),
        sorts: vec![
            OccurrenceSortSpec {
                name: "S".into(),
                elements: vec!["a".into(), "b".into(), "c".into()],
                is_fixed_value: false,
            },
            OccurrenceSortSpec {
                name: "V".into(),
                elements: vec!["0".into(), "1".into()],
                is_fixed_value: true,
            },
        ],
        operations: vec![OccurrenceOpSpec {
            name: "f".into(),
            arg_sorts: vec!["S".into()],
            out_sort: "V".into(),
            is_total: false,
        }],
        relations: vec![],
        identity_requests: vec![],
        op_records: vec![
            OpOutputRecord {
                op_name: "f".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["b".into()],
                out_sort: "V".into(),
                output: "0".into(),
                positive: true,
            },
            OpOutputRecord {
                op_name: "f".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["c".into()],
                out_sort: "V".into(),
                output: "1".into(),
                positive: true,
            },
        ],
        pred_records: vec![],
        base_readings: vec![],
        context_closed_17_5: false,
        explicit_contexts: vec![],
        preserve_full_domains: vec![],
        initial_readouts: vec![],
        provenance: prov(),
        max_congruence_steps: 0,
        max_partitions: 0,
        undeclared_unobserved_slots: vec![],
    };
    let out = solve_occurrence_task(&validate_occurrence_task(spec).unwrap());
    assert_eq!(out.verdict, Verdict::Established);
    let occ = out.occurrence.unwrap();
    // {a,b}|{c} と {a,c}|{b} と離散分割 {a}|{b}|{c} が健全であり、単一最粗商は存在しない
    assert_eq!(occ.sound_identifications_count, Some(3));
    assert!(!occ.coarsest_sound_exists);
    assert!(occ.coarsest_sound_classes.is_none());
}

#[test]
fn ch17_example17_12_and_17_13_attribute_kappa_and_request_collision() {
    // 数学本文 例 17.12: E = {a,b,c,d}, T(a)=a, T(b)=c, T(c)=c, T(d)=d
    // o(a)=o(b)=o(c)=0, o(d)=1 により文脈同値 ≈_V = {a,b,c} | {d}
    // 初期読み出し p(a)=p(b)=0, p(c)=1, p(d)=0 より、評価分離 kappa = |{a,b,d} / ≈_V| = 2。
    // 一方、T 保存と θ ⊆ ker p かつ a~b => T(a)=a ~ c=T(b) (p(a)!=p(c)) のため、操作保存最小 kappa = 3。
    let base = OccurrenceTaskSpec {
        name: "ex_17_12".into(),
        sorts: vec![OccurrenceSortSpec {
            name: "S".into(),
            elements: vec!["a".into(), "b".into(), "c".into(), "d".into()],
            is_fixed_value: false,
        }],
        operations: vec![OccurrenceOpSpec {
            name: "T".into(),
            arg_sorts: vec!["S".into()],
            out_sort: "S".into(),
            is_total: true,
        }],
        relations: vec![],
        identity_requests: vec![],
        op_records: vec![
            OpOutputRecord {
                op_name: "T".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["a".into()],
                out_sort: "S".into(),
                output: "a".into(),
                positive: true,
            },
            OpOutputRecord {
                op_name: "T".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["b".into()],
                out_sort: "S".into(),
                output: "c".into(),
                positive: true,
            },
            OpOutputRecord {
                op_name: "T".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["c".into()],
                out_sort: "S".into(),
                output: "c".into(),
                positive: true,
            },
            OpOutputRecord {
                op_name: "T".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["d".into()],
                out_sort: "S".into(),
                output: "d".into(),
                positive: true,
            },
        ],
        pred_records: vec![],
        base_readings: vec![OccurrenceReadingSpec {
            name: "o".into(),
            sort: "S".into(),
            values: BTreeMap::from([
                ("a".into(), Some("0".into())),
                ("b".into(), Some("0".into())),
                ("c".into(), Some("0".into())),
                ("d".into(), Some("1".into())),
            ]),
        }],
        context_closed_17_5: true,
        explicit_contexts: vec![],
        preserve_full_domains: vec![],
        initial_readouts: vec![OccurrenceInitialReadoutSpec {
            sort: "S".into(),
            values: BTreeMap::from([
                ("a".into(), "0".into()),
                ("b".into(), "0".into()),
                ("c".into(), "1".into()),
                ("d".into(), "0".into()),
            ]),
        }],
        provenance: prov(),
        max_congruence_steps: 0,
        max_partitions: 0,
        undeclared_unobserved_slots: vec![],
    };

    let out = solve_occurrence_task(&validate_occurrence_task(base.clone()).unwrap());
    assert_eq!(out.verdict, Verdict::Established);
    let occ = out.occurrence.unwrap();
    assert_eq!(
        occ.context_equivalence_classes["S"],
        vec![
            vec!["a".to_owned(), "b".to_owned(), "c".to_owned()],
            vec!["d".to_owned()],
        ]
    );
    let attr = occ.attribute_realization.unwrap();
    assert!(attr.sound_identification_exists);
    assert_eq!(attr.eval_separation_kappa["S"], 2);
    assert_eq!(
        attr.minimal_sound_kappa_tuples,
        vec![BTreeMap::from([("S".into(), 3)])]
    );
    assert!(
        attr.reevaluation
            .as_ref()
            .is_some_and(|r| r.checked && r.matched)
    );
    let p0_vals: BTreeSet<usize> = ["a", "b", "d"]
        .into_iter()
        .map(|e| attr.selected_attribute_assignment["S"][e])
        .collect();
    assert_eq!(p0_vals.len(), 3);

    // 要求 (a, b) ∈ ker(p) ∩ ≈_V を追加すると T(a)=a ~ c=T(b) が p(a)!=p(c) で破綻する
    let mut with_req = base;
    with_req
        .identity_requests
        .push(("S".into(), "a".into(), "b".into()));
    let out_req = solve_occurrence_task(&validate_occurrence_task(with_req).unwrap());
    assert_eq!(out_req.verdict, Verdict::Refuted);
    let attr_fail = out_req.occurrence.unwrap().attribute_realization.unwrap();
    assert!(!attr_fail.sound_identification_exists);
    assert_eq!(attr_fail.eval_separation_kappa["S"], 2);
    assert!(
        attr_fail
            .failure_reason
            .as_deref()
            .is_some_and(|msg| msg.contains("ker(p_s)"))
    );

    // 例 17.13: 別名（x0, x1 同一）+ 多解釈タグ付き（y0, y1 を初期読出し同一ファイバ内で区別）
    let ex17_13 = OccurrenceTaskSpec {
        name: "ex_17_13".into(),
        sorts: vec![
            OccurrenceSortSpec {
                name: "S".into(),
                elements: vec!["x0".into(), "x1".into(), "y0".into(), "y1".into()],
                is_fixed_value: false,
            },
            OccurrenceSortSpec {
                name: "Out".into(),
                elements: vec!["ok".into(), "err".into()],
                is_fixed_value: true,
            },
        ],
        operations: vec![],
        relations: vec![OccurrenceRelSpec {
            name: "tag".into(),
            arg_sorts: vec!["S".into()],
        }],
        identity_requests: vec![("S".into(), "x0".into(), "x1".into())],
        op_records: vec![],
        pred_records: vec![],
        base_readings: vec![OccurrenceReadingSpec {
            name: "mode".into(),
            sort: "S".into(),
            values: BTreeMap::from([
                ("x0".into(), Some("m1".into())),
                ("x1".into(), Some("m1".into())),
                ("y0".into(), Some("m1".into())),
                ("y1".into(), Some("m2".into())),
            ]),
        }],
        context_closed_17_5: false,
        explicit_contexts: vec![],
        preserve_full_domains: vec![],
        initial_readouts: vec![OccurrenceInitialReadoutSpec {
            sort: "S".into(),
            values: BTreeMap::from([
                ("x0".into(), "syn_x".into()),
                ("x1".into(), "syn_x".into()),
                ("y0".into(), "syn_y".into()),
                ("y1".into(), "syn_y".into()),
            ]),
        }],
        provenance: prov(),
        max_congruence_steps: 0,
        max_partitions: 0,
        undeclared_unobserved_slots: vec![],
    };
    let out13 = solve_occurrence_task(&validate_occurrence_task(ex17_13).unwrap());
    assert_eq!(out13.verdict, Verdict::Established);
    let attr13 = out13.occurrence.unwrap().attribute_realization.unwrap();
    assert!(attr13.sound_identification_exists);
    // syn_x は 1 値で済み、syn_y は y0(m1) と y1(m2) を分けるため 2 値が必要
    assert_eq!(attr13.minimal_sound_kappa_tuples[0]["S"], 2);
}

#[test]
fn ch17_undetermined_on_unobserved_and_partition_bound() {
    let unobs = OccurrenceTaskSpec {
        name: "unobs_occ".into(),
        sorts: vec![OccurrenceSortSpec {
            name: "S".into(),
            elements: vec!["a".into(), "b".into()],
            is_fixed_value: false,
        }],
        operations: vec![],
        relations: vec![],
        identity_requests: vec![],
        op_records: vec![],
        pred_records: vec![],
        base_readings: vec![],
        context_closed_17_5: false,
        explicit_contexts: vec![],
        preserve_full_domains: vec![],
        initial_readouts: vec![],
        provenance: prov(),
        max_congruence_steps: 0,
        max_partitions: 0,
        undeclared_unobserved_slots: vec!["slot_missing".into()],
    };
    let out_unobs = solve_occurrence_task(&validate_occurrence_task(unobs).unwrap());
    assert!(matches!(
        out_unobs.verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { .. })
    ));

    let bounded = OccurrenceTaskSpec {
        name: "bound_occ".into(),
        sorts: vec![OccurrenceSortSpec {
            name: "S".into(),
            elements: vec!["a".into(), "b".into(), "c".into(), "d".into()],
            is_fixed_value: false,
        }],
        operations: vec![],
        relations: vec![],
        identity_requests: vec![],
        op_records: vec![],
        pred_records: vec![],
        base_readings: vec![],
        context_closed_17_5: false,
        explicit_contexts: vec![],
        preserve_full_domains: vec![],
        initial_readouts: vec![],
        provenance: prov(),
        max_congruence_steps: 0,
        max_partitions: 2,
        undeclared_unobserved_slots: vec![],
    };
    let out_bound = solve_occurrence_task(&validate_occurrence_task(bounded).unwrap());
    assert!(matches!(
        out_bound.verdict,
        Verdict::Undetermined(SilenceReason::FiniteEnumerationOutOfScope { .. })
    ));
}

#[test]
fn ch17_setting17_5_relations_negative_guards_and_bot_reading_soundness() {
    // 1. 関係表による設定 17.5 反復細分と分離文脈生成
    let rel_task = OccurrenceTaskSpec {
        name: "setting17_5_rel_sep".into(),
        sorts: vec![OccurrenceSortSpec {
            name: "S".into(),
            elements: vec!["a0".into(), "a1".into(), "b0".into()],
            is_fixed_value: false,
        }],
        operations: vec![],
        relations: vec![OccurrenceRelSpec {
            name: "R".into(),
            arg_sorts: vec!["S".into()],
        }],
        identity_requests: vec![],
        op_records: vec![],
        pred_records: vec![
            PredicateRecord {
                kind: PredicateRecordKind::Relation,
                name: "R".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["a0".into()],
                positive: true,
            },
            PredicateRecord {
                kind: PredicateRecordKind::Relation,
                name: "R".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["a1".into()],
                positive: true,
            },
            PredicateRecord {
                kind: PredicateRecordKind::Relation,
                name: "R".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["b0".into()],
                positive: false,
            },
        ],
        base_readings: vec![],
        context_closed_17_5: true,
        explicit_contexts: vec![],
        preserve_full_domains: vec![],
        initial_readouts: vec![],
        provenance: prov(),
        max_congruence_steps: 0,
        max_partitions: 0,
        undeclared_unobserved_slots: vec![],
    };
    let rel_out = solve_occurrence_task(&validate_occurrence_task(rel_task).unwrap());
    assert_eq!(rel_out.verdict, Verdict::Established);
    let rel_occ = rel_out.occurrence.unwrap();
    assert_eq!(
        rel_occ.context_equivalence_classes["S"],
        vec![
            vec!["a0".to_owned(), "a1".to_owned()],
            vec!["b0".to_owned()],
        ]
    );
    assert!(
        rel_occ
            .separating_contexts
            .iter()
            .any(|sc| sc.context_expr == "R(x)" && sc.verified)
    );

    // 1b. 非代表元 (a1, b1) を同一視要求したときの代表元 (a0, b0) 経由 witness 検索
    let nonrep_task = OccurrenceTaskSpec {
        name: "setting17_5_nonrep_witness".into(),
        sorts: vec![OccurrenceSortSpec {
            name: "S".into(),
            elements: vec!["a0".into(), "a1".into(), "b0".into(), "b1".into()],
            is_fixed_value: false,
        }],
        operations: vec![],
        relations: vec![],
        identity_requests: vec![("S".into(), "a1".into(), "b1".into())],
        op_records: vec![],
        pred_records: vec![],
        base_readings: vec![OccurrenceReadingSpec {
            name: "o".into(),
            sort: "S".into(),
            values: BTreeMap::from([
                ("a0".into(), Some("0".into())),
                ("a1".into(), Some("0".into())),
                ("b0".into(), Some("1".into())),
                ("b1".into(), Some("1".into())),
            ]),
        }],
        context_closed_17_5: true,
        explicit_contexts: vec![],
        preserve_full_domains: vec![],
        initial_readouts: vec![],
        provenance: prov(),
        max_congruence_steps: 0,
        max_partitions: 0,
        undeclared_unobserved_slots: vec![],
    };
    let nonrep_out = solve_occurrence_task(&validate_occurrence_task(nonrep_task).unwrap());
    assert_eq!(nonrep_out.verdict, Verdict::Refuted);
    let nonrep_occ = nonrep_out.occurrence.unwrap();
    let sep_col = nonrep_occ
        .collisions
        .iter()
        .find(|c| c.kind == "context_separation_conflict")
        .expect("context separation collision expected");
    assert!(!sep_col.detail.contains("context_mismatch"));
    assert!(sep_col.detail.contains("o(x)"));

    // 2. 設定 17.5 で G_e^- が非空なら適用条件外で Undetermined
    let neg_out_task = OccurrenceTaskSpec {
        name: "setting17_5_neg_op".into(),
        sorts: vec![OccurrenceSortSpec {
            name: "S".into(),
            elements: vec!["a".into(), "b".into()],
            is_fixed_value: false,
        }],
        operations: vec![OccurrenceOpSpec {
            name: "T".into(),
            arg_sorts: vec!["S".into()],
            out_sort: "S".into(),
            is_total: true,
        }],
        relations: vec![],
        identity_requests: vec![],
        op_records: vec![
            OpOutputRecord {
                op_name: "T".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["a".into()],
                out_sort: "S".into(),
                output: "a".into(),
                positive: true,
            },
            OpOutputRecord {
                op_name: "T".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["b".into()],
                out_sort: "S".into(),
                output: "b".into(),
                positive: true,
            },
            OpOutputRecord {
                op_name: "T".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["b".into()],
                out_sort: "S".into(),
                output: "a".into(),
                positive: false,
            },
        ],
        pred_records: vec![],
        base_readings: vec![],
        context_closed_17_5: true,
        explicit_contexts: vec![],
        preserve_full_domains: vec![],
        initial_readouts: vec![],
        provenance: prov(),
        max_congruence_steps: 0,
        max_partitions: 0,
        undeclared_unobserved_slots: vec![],
    };
    assert!(matches!(
        solve_occurrence_task(&validate_occurrence_task(neg_out_task).unwrap()).verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { .. })
    ));

    // 3. 設定 17.5 で is_total 操作に負の定義域記録があれば適用条件外で Undetermined
    let total_dom_neg = OccurrenceTaskSpec {
        name: "setting17_5_total_dom_neg".into(),
        sorts: vec![OccurrenceSortSpec {
            name: "S".into(),
            elements: vec!["a".into(), "b".into()],
            is_fixed_value: false,
        }],
        operations: vec![OccurrenceOpSpec {
            name: "T".into(),
            arg_sorts: vec!["S".into()],
            out_sort: "S".into(),
            is_total: true,
        }],
        relations: vec![],
        identity_requests: vec![],
        op_records: vec![OpOutputRecord {
            op_name: "T".into(),
            arg_sorts: vec!["S".into()],
            args: vec!["a".into()],
            out_sort: "S".into(),
            output: "a".into(),
            positive: true,
        }],
        pred_records: vec![PredicateRecord {
            kind: PredicateRecordKind::Domain,
            name: "T".into(),
            arg_sorts: vec!["S".into()],
            args: vec!["b".into()],
            positive: false,
        }],
        base_readings: vec![],
        context_closed_17_5: true,
        explicit_contexts: vec![],
        preserve_full_domains: vec![],
        initial_readouts: vec![],
        provenance: prov(),
        max_congruence_steps: 0,
        max_partitions: 0,
        undeclared_unobserved_slots: vec![],
    };
    assert!(matches!(
        solve_occurrence_task(&validate_occurrence_task(total_dom_neg).unwrap()).verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { .. })
    ));

    // 4. 一般有限系で読取りに明示未定義 None (bot_c) と Some("0") がある場合、混同する同定は健全でない
    let bot_sep = OccurrenceTaskSpec {
        name: "general_bot_reading".into(),
        sorts: vec![OccurrenceSortSpec {
            name: "S".into(),
            elements: vec!["a".into(), "b".into()],
            is_fixed_value: false,
        }],
        operations: vec![],
        relations: vec![],
        identity_requests: vec![],
        op_records: vec![],
        pred_records: vec![],
        base_readings: vec![OccurrenceReadingSpec {
            name: "c".into(),
            sort: "S".into(),
            values: BTreeMap::from([("a".into(), Some("0".into())), ("b".into(), None)]),
        }],
        context_closed_17_5: false,
        explicit_contexts: vec![],
        preserve_full_domains: vec![],
        initial_readouts: vec![],
        provenance: prov(),
        max_congruence_steps: 0,
        max_partitions: 0,
        undeclared_unobserved_slots: vec![],
    };
    let bot_out = solve_occurrence_task(&validate_occurrence_task(bot_sep).unwrap());
    assert_eq!(bot_out.verdict, Verdict::Established);
    let bot_occ = bot_out.occurrence.unwrap();
    assert_eq!(bot_occ.sound_identifications_count, Some(1));
    assert_eq!(
        bot_occ.coarsest_sound_classes.unwrap()["S"],
        vec![vec!["a".to_owned()], vec!["b".to_owned()]]
    );

    // 5. 一般有限系では eval_separation_kappa が操作や要求でなく許容評価文脈のみで定まり、
    // 設定 17.5 では sound_identifications_count が None かつ ker(p) 細分の上限超過で Undetermined になる。
    let mut kappa_general = rel_task_gen_setup();
    kappa_general
        .initial_readouts
        .push(OccurrenceInitialReadoutSpec {
            sort: "S".into(),
            values: BTreeMap::from([("a".into(), "0".into()), ("b".into(), "0".into())]),
        });
    let kg_out = solve_occurrence_task(&validate_occurrence_task(kappa_general).unwrap());
    let kg_occ = kg_out.occurrence.unwrap();
    assert_eq!(
        kg_occ.context_equivalence_classes["S"],
        vec![vec!["a", "b"]]
    );
    assert_eq!(
        kg_occ.attribute_realization.unwrap().eval_separation_kappa["S"],
        1
    );

    // 6. ker(p) 追加細分時に max_partitions=1 で上限超過すると Refuted でなく FiniteEnumerationOutOfScope
    let kerp_bound = OccurrenceTaskSpec {
        name: "kerp_bound".into(),
        sorts: vec![OccurrenceSortSpec {
            name: "S".into(),
            elements: vec!["a".into(), "b".into(), "c".into()],
            is_fixed_value: false,
        }],
        operations: vec![OccurrenceOpSpec {
            name: "T".into(),
            arg_sorts: vec!["S".into()],
            out_sort: "S".into(),
            is_total: true,
        }],
        relations: vec![],
        identity_requests: vec![],
        op_records: vec![
            OpOutputRecord {
                op_name: "T".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["a".into()],
                out_sort: "S".into(),
                output: "a".into(),
                positive: true,
            },
            OpOutputRecord {
                op_name: "T".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["b".into()],
                out_sort: "S".into(),
                output: "c".into(),
                positive: true,
            },
            OpOutputRecord {
                op_name: "T".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["c".into()],
                out_sort: "S".into(),
                output: "c".into(),
                positive: true,
            },
        ],
        pred_records: vec![],
        base_readings: vec![OccurrenceReadingSpec {
            name: "o".into(),
            sort: "S".into(),
            values: BTreeMap::from([
                ("a".into(), Some("0".into())),
                ("b".into(), Some("0".into())),
                ("c".into(), Some("0".into())),
            ]),
        }],
        context_closed_17_5: true,
        explicit_contexts: vec![],
        preserve_full_domains: vec![],
        initial_readouts: vec![OccurrenceInitialReadoutSpec {
            sort: "S".into(),
            values: BTreeMap::from([
                ("a".into(), "0".into()),
                ("b".into(), "0".into()),
                ("c".into(), "1".into()),
            ]),
        }],
        provenance: prov(),
        max_congruence_steps: 0,
        max_partitions: 1,
        undeclared_unobserved_slots: vec![],
    };
    assert!(matches!(
        solve_occurrence_task(&validate_occurrence_task(kerp_bound).unwrap()).verdict,
        Verdict::Undetermined(SilenceReason::FiniteEnumerationOutOfScope { .. })
    ));
}

fn rel_task_gen_setup() -> OccurrenceTaskSpec {
    OccurrenceTaskSpec {
        name: "general_eval_kappa".into(),
        sorts: vec![
            OccurrenceSortSpec {
                name: "S".into(),
                elements: vec!["a".into(), "b".into()],
                is_fixed_value: false,
            },
            OccurrenceSortSpec {
                name: "V".into(),
                elements: vec!["0".into(), "1".into()],
                is_fixed_value: true,
            },
        ],
        operations: vec![OccurrenceOpSpec {
            name: "f".into(),
            arg_sorts: vec!["S".into()],
            out_sort: "V".into(),
            is_total: true,
        }],
        relations: vec![],
        identity_requests: vec![],
        op_records: vec![
            OpOutputRecord {
                op_name: "f".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["a".into()],
                out_sort: "V".into(),
                output: "0".into(),
                positive: true,
            },
            OpOutputRecord {
                op_name: "f".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["b".into()],
                out_sort: "V".into(),
                output: "1".into(),
                positive: true,
            },
        ],
        pred_records: vec![],
        base_readings: vec![],
        context_closed_17_5: false,
        explicit_contexts: vec![],
        preserve_full_domains: vec![],
        initial_readouts: vec![],
        provenance: prov(),
        max_congruence_steps: 0,
        max_partitions: 0,
        undeclared_unobserved_slots: vec![],
    }
}
