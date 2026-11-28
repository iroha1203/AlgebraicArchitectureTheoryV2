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
    // 例 17.12: T(c)=b, T(b)=a, T(a)=a, 評価 obs(a)=1, obs(b)=0, obs(c)=0、初期読み出しは定数 "_"
    // 評価分離だけなら 2 値（{b,c}, {a}）だが、T 保存では 3 値（{a}, {b}, {c}）が必要。
    let base = OccurrenceTaskSpec {
        name: "ex_17_12".into(),
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
                args: vec!["c".into()],
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
                positive: true,
            },
            OpOutputRecord {
                op_name: "T".into(),
                arg_sorts: vec!["S".into()],
                args: vec!["a".into()],
                out_sort: "S".into(),
                output: "a".into(),
                positive: true,
            },
        ],
        pred_records: vec![],
        base_readings: vec![OccurrenceReadingSpec {
            name: "eval".into(),
            sort: "S".into(),
            values: BTreeMap::from([
                ("a".into(), Some("1".into())),
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
                ("a".into(), "u".into()),
                ("b".into(), "u".into()),
                ("c".into(), "u".into()),
            ]),
        }],
        provenance: prov(),
        max_congruence_steps: 0,
        max_partitions: 0,
        undeclared_unobserved_slots: vec![],
    };

    let out = solve_occurrence_task(&validate_occurrence_task(base.clone()).unwrap());
    assert_eq!(out.verdict, Verdict::Established);
    let attr = out.occurrence.unwrap().attribute_realization.unwrap();
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
    let assigned_vals: BTreeSet<usize> = attr.selected_attribute_assignment["S"]
        .values()
        .copied()
        .collect();
    assert_eq!(assigned_vals.len(), 3);

    // 要求 b ~ c を追加すると T(b)=a vs T(c)=b => a ~ b が評価 obs で衝突する
    let mut with_req = base;
    with_req
        .identity_requests
        .push(("S".into(), "b".into(), "c".into()));
    let out_req = solve_occurrence_task(&validate_occurrence_task(with_req).unwrap());
    assert_eq!(out_req.verdict, Verdict::Refuted);
    let attr_fail = out_req.occurrence.unwrap().attribute_realization.unwrap();
    assert!(!attr_fail.sound_identification_exists);
    assert!(attr_fail.failure_reason.is_some());

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
