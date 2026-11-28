//! Phase 5 離散・代数計算核（`congruence`, `partition`, `hitting_set`, `snf`）の単体テスト。

use super::congruence::{
    CollisionKind, CongruenceInput, CongruenceSort, DEFAULT_MAX_CONGRUENCE_STEPS, OpOutputRecord,
    PredicateRecord, PredicateRecordKind, compute_congruence_closure, verify_collision_witness,
};
use super::hitting_set::{
    DEFAULT_MAX_HITTING_SET_RESULTS, DEFAULT_MAX_HITTING_SET_STEPS, HittingSetInput,
    HittingSetOutcome, enumerate_minimal_hitting_sets,
};
use super::partition::{
    BaseReading, PartialOpTable, RefinementInput, enumerate_set_partitions, partition_refines,
    refine_partition,
};
use super::poly::AlgebraError;
use super::scalar::Rat;
use super::snf::{SnfFactorizationQ, SnfFactorizationZ};
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet};

#[test]
fn congruence_closure_detects_functionality_and_fixed_collision_with_verified_derivation() {
    let input = CongruenceInput {
        sorts: vec![
            CongruenceSort {
                name: "S".to_owned(),
                elements: vec!["x".into(), "x_prime".into(), "y".into(), "y_prime".into()],
                is_fixed_value: false,
            },
            CongruenceSort {
                name: "Val".to_owned(),
                elements: vec!["0".into(), "1".into()],
                is_fixed_value: true,
            },
        ],
        requests: vec![("S".into(), "x".into(), "x_prime".into())],
        op_records: vec![
            OpOutputRecord {
                op_name: "T".into(),
                arg_sorts: vec!["S".into()],
                out_sort: "S".into(),
                args: vec!["x".into()],
                output: "y".into(),
                positive: true,
            },
            OpOutputRecord {
                op_name: "T".into(),
                arg_sorts: vec!["S".into()],
                out_sort: "S".into(),
                args: vec!["x_prime".into()],
                output: "y_prime".into(),
                positive: true,
            },
            OpOutputRecord {
                op_name: "obs".into(),
                arg_sorts: vec!["S".into()],
                out_sort: "Val".into(),
                args: vec!["y".into()],
                output: "0".into(),
                positive: true,
            },
            OpOutputRecord {
                op_name: "obs".into(),
                arg_sorts: vec!["S".into()],
                out_sort: "Val".into(),
                args: vec!["y_prime".into()],
                output: "1".into(),
                positive: true,
            },
        ],
        predicate_records: vec![],
        max_steps: DEFAULT_MAX_CONGRUENCE_STEPS,
    };

    let res = compute_congruence_closure(&input).expect("congruence closure succeeds");
    assert!(res.derivation_verified);
    assert_eq!(res.collisions.len(), 1);
    assert!(matches!(
        res.collisions[0].kind,
        CollisionKind::FixedValueCollision { ref sort, .. } if sort == "Val"
    ));
    assert!(verify_collision_witness(&input, &res.collisions[0]));
}

#[test]
fn congruence_closure_detects_pos_neg_domain_and_output_collision() {
    let input = CongruenceInput {
        sorts: vec![CongruenceSort {
            name: "S".to_owned(),
            elements: vec!["a".into(), "b".into()],
            is_fixed_value: false,
        }],
        requests: vec![("S".into(), "a".into(), "b".into())],
        op_records: vec![
            OpOutputRecord {
                op_name: "id".into(),
                arg_sorts: vec!["S".into()],
                out_sort: "S".into(),
                args: vec!["a".into()],
                output: "a".into(),
                positive: true,
            },
            OpOutputRecord {
                op_name: "id".into(),
                arg_sorts: vec!["S".into()],
                out_sort: "S".into(),
                args: vec!["b".into()],
                output: "a".into(),
                positive: false,
            },
        ],
        predicate_records: vec![
            PredicateRecord {
                name: "p".into(),
                kind: PredicateRecordKind::Domain,
                arg_sorts: vec!["S".into()],
                args: vec!["a".into()],
                positive: true,
            },
            PredicateRecord {
                name: "p".into(),
                kind: PredicateRecordKind::Domain,
                arg_sorts: vec!["S".into()],
                args: vec!["b".into()],
                positive: false,
            },
        ],
        max_steps: DEFAULT_MAX_CONGRUENCE_STEPS,
    };

    let res = compute_congruence_closure(&input).expect("closure succeeds");
    assert!(res.derivation_verified);
    assert_eq!(res.collisions.len(), 2);
}

#[test]
fn partition_refinement_produces_verified_separating_context() {
    // 命題 17.8 の例: E = {a,b,c}, T(a)=a, T(b)=c, T(c)=c, o(a)=o(b)=0, o(c)=1
    let input = RefinementInput {
        sorts: BTreeMap::from([("E".into(), vec!["a".into(), "b".into(), "c".into()])]),
        fixed_sorts: BTreeSet::new(),
        base_readings: vec![BaseReading {
            name: "o".into(),
            sort: "E".into(),
            values: BTreeMap::from([
                ("a".into(), Some("0".into())),
                ("b".into(), Some("0".into())),
                ("c".into(), Some("1".into())),
            ]),
        }],
        ops: vec![PartialOpTable {
            name: "T".into(),
            arg_sorts: vec!["E".into()],
            out_sort: "E".into(),
            entries: BTreeMap::from([
                (vec!["a".into()], Some("a".into())),
                (vec!["b".into()], Some("c".into())),
                (vec!["c".into()], Some("c".into())),
            ]),
        }],
        max_iterations: 16,
    };

    let res = refine_partition(&input).expect("refinement succeeds");
    assert!(res.all_witnesses_verified);
    assert_eq!(
        res.classes["E"],
        vec![
            vec!["a".to_owned()],
            vec!["b".to_owned()],
            vec!["c".to_owned()],
        ]
    );
    let ab = res
        .witnesses
        .iter()
        .find(|w| w.lhs == "a" && w.rhs == "b")
        .expect("a vs b witness");
    assert_eq!(ab.context_expr, "o(T(x))");
    assert_eq!(ab.lhs_value.as_deref(), Some("0"));
    assert_eq!(ab.rhs_value.as_deref(), Some("1"));

    // 3 要素集合分割は Bell(3) = 5
    let parts = enumerate_set_partitions(&["a".into(), "b".into(), "c".into()], 10).unwrap();
    assert_eq!(parts.len(), 5);
    assert!(partition_refines(
        &[vec!["a".into()], vec!["b".into()], vec!["c".into()]],
        &parts[0]
    ));
}

#[test]
fn hitting_set_enumerates_minimal_sets_weights_and_empty_hyperedge() {
    // 例 19.13 相当: {{w, xi}, {w, eta}} -> {w}, {xi, eta}
    let res = enumerate_minimal_hitting_sets(&HittingSetInput {
        universe: vec!["w".into(), "xi".into(), "eta".into()],
        hyperedges: vec![
            vec!["w".into(), "xi".into()],
            vec!["w".into(), "eta".into()],
        ],
        weights: Some(BTreeMap::from([
            ("w".into(), Rat::from_int(5)),
            ("xi".into(), Rat::from_int(2)),
            ("eta".into(), Rat::from_int(2)),
        ])),
        max_steps: DEFAULT_MAX_HITTING_SET_STEPS,
        max_results: DEFAULT_MAX_HITTING_SET_RESULTS,
    })
    .expect("hitting set succeeds");

    match res {
        HittingSetOutcome::Enumerated {
            minimal_sets,
            min_cost_sets,
            verified,
            ..
        } => {
            assert!(verified);
            assert_eq!(
                minimal_sets,
                vec![
                    vec!["eta".to_owned(), "xi".to_owned()],
                    vec!["w".to_owned()],
                ]
            );
            assert_eq!(
                min_cost_sets,
                vec![(vec!["eta".to_owned(), "xi".to_owned()], Rat::from_int(4))]
            );
        }
        other => panic!("expected Enumerated, got {other:?}"),
    }

    let empty = enumerate_minimal_hitting_sets(&HittingSetInput {
        universe: vec!["a".into()],
        hyperedges: vec![vec![]],
        weights: None,
        max_steps: DEFAULT_MAX_HITTING_SET_STEPS,
        max_results: DEFAULT_MAX_HITTING_SET_RESULTS,
    })
    .unwrap();
    assert_eq!(empty, HittingSetOutcome::EmptyHyperedge { edge_index: 0 });
}

#[test]
fn snf_z_and_q_verify_umv_and_solve_multiple_rhs() {
    // 定理 19.7: 2p = b, b = 2, 4, 3
    let m = vec![vec![BigInt::from(2)]];
    let snf = SnfFactorizationZ::compute(&m, 1).expect("SNF Z succeeds");
    assert!(snf.umv_verified);
    assert!(snf.unimodular_verified);
    assert!(snf.divisibility_verified);
    assert_eq!(snf.diagonals, vec![BigInt::from(2)]);
    assert_eq!(snf.cokernel_torsion, vec![BigInt::from(2)]);

    let s2 = snf.solve_rhs(&m, &[BigInt::from(2)]).unwrap();
    assert!(s2.solvable && s2.reeval_verified);
    assert_eq!(s2.particular, Some(vec![BigInt::from(1)]));

    let s4 = snf.solve_rhs(&m, &[BigInt::from(4)]).unwrap();
    assert!(s4.solvable && s4.reeval_verified);
    assert_eq!(s4.particular, Some(vec![BigInt::from(2)]));

    let s3 = snf.solve_rhs(&m, &[BigInt::from(3)]).unwrap();
    assert!(!s3.solvable && s3.reeval_verified);
    assert_eq!(s3.divisor, Some(BigInt::from(2)));

    // 2x3 Z 行列で非自明な ker と coker を確認
    let m2 = vec![
        vec![BigInt::from(2), BigInt::from(4), BigInt::from(6)],
        vec![BigInt::from(4), BigInt::from(8), BigInt::from(12)],
    ];
    let snf2 = SnfFactorizationZ::compute(&m2, 3).unwrap();
    assert!(snf2.umv_verified && snf2.unimodular_verified && snf2.divisibility_verified);
    assert_eq!(snf2.rank, 1);
    assert_eq!(snf2.kernel_basis.len(), 2);
    assert_eq!(snf2.cokernel_free_rank, 1);
    let sol2 = snf2
        .solve_rhs(&m2, &[BigInt::from(2), BigInt::from(4)])
        .unwrap();
    assert!(sol2.solvable && sol2.reeval_verified);

    // Q 上 SNF
    let mq = vec![
        vec![Rat::from_int(1), Rat::from_int(2)],
        vec![Rat::from_int(2), Rat::from_int(4)],
    ];
    let snfq = SnfFactorizationQ::compute(&mq, 2).unwrap();
    assert!(snfq.umv_verified && snfq.invertible_verified);
    assert_eq!(snfq.rank, 1);
    let sq_ok = snfq
        .solve_rhs(&mq, &[Rat::from_int(3), Rat::from_int(6)])
        .unwrap();
    assert!(sq_ok.solvable && sq_ok.reeval_verified);
    let sq_bad = snfq
        .solve_rhs(&mq, &[Rat::from_int(3), Rat::from_int(5)])
        .unwrap();
    assert!(!sq_bad.solvable && sq_bad.reeval_verified);

    // 上限超過エラーの負系確認
    let err = enumerate_set_partitions(&["a".into(), "b".into(), "c".into()], 2);
    assert!(matches!(err, Err(AlgebraError::OutOfScope { .. })));
}

#[test]
fn congruence_closure_multi_hop_reverse_request_and_functionality_derivation() {
    let input = CongruenceInput {
        sorts: vec![
            CongruenceSort {
                name: "S".into(),
                elements: vec!["a".into(), "b".into(), "c".into(), "d".into()],
                is_fixed_value: false,
            },
            CongruenceSort {
                name: "V".into(),
                elements: vec!["0".into(), "1".into()],
                is_fixed_value: true,
            },
        ],
        // 逆向き要求を含む多段連鎖: b ~ a, b ~ c, d ~ c => a ~ d
        requests: vec![
            ("S".into(), "b".into(), "a".into()),
            ("S".into(), "b".into(), "c".into()),
            ("S".into(), "d".into(), "c".into()),
        ],
        op_records: vec![
            OpOutputRecord {
                op_name: "f".into(),
                arg_sorts: vec!["S".into()],
                out_sort: "V".into(),
                args: vec!["a".into()],
                output: "0".into(),
                positive: true,
            },
            OpOutputRecord {
                op_name: "f".into(),
                arg_sorts: vec!["S".into()],
                out_sort: "V".into(),
                args: vec!["d".into()],
                output: "1".into(),
                positive: true,
            },
        ],
        predicate_records: vec![],
        max_steps: DEFAULT_MAX_CONGRUENCE_STEPS,
    };
    let res = compute_congruence_closure(&input).expect("multi-hop closure succeeds");
    assert!(res.derivation_verified);
    assert_eq!(res.collisions.len(), 1);
    assert!(verify_collision_witness(&input, &res.collisions[0]));
}

#[test]
fn hitting_set_empty_hyperedges_returns_single_empty_set() {
    let res = enumerate_minimal_hitting_sets(&HittingSetInput {
        universe: vec!["x".into(), "y".into()],
        hyperedges: vec![],
        weights: Some(BTreeMap::from([
            ("x".into(), Rat::from_int(3)),
            ("y".into(), Rat::from_int(2)),
        ])),
        max_steps: DEFAULT_MAX_HITTING_SET_STEPS,
        max_results: DEFAULT_MAX_HITTING_SET_RESULTS,
    })
    .expect("empty hyperedges succeeds");

    match res {
        HittingSetOutcome::Enumerated {
            minimal_sets,
            min_cost_sets,
            verified,
            ..
        } => {
            assert!(verified);
            assert_eq!(minimal_sets, vec![Vec::<String>::new()]);
            assert_eq!(
                min_cost_sets,
                vec![(Vec::<String>::new(), Rat::from_int(0))]
            );
        }
        other => panic!("expected Enumerated, got {other:?}"),
    }
}
