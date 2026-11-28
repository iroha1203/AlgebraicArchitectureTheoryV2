//! 第19章前半（`shigure_revision`）計算核の単体・定理テスト。

use super::revision::solve_revision_task;
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::revision::{
    RevisionConstraintSpec, RevisionCoordSpec, RevisionEvalProbe, RevisionKind, RevisionPredicate,
    RevisionSideSpec, RevisionTaskSpec, SnfRevisionSpec, validate_revision_task,
};
use crate::ir::term::{CoeffDomain, ScalarLit};
use std::collections::BTreeMap;

fn prov() -> Provenance {
    Provenance::new(
        vec![SourceRef::new("ch19_rev_test", OriginKind::StaticAnalysis)],
        vec![MathClause::AatCh19Thm19Dot4],
    )
}

#[test]
fn ch19_example19_5_invalidation_cone_outside_projection_and_inconsistent_extension() {
    // 例 19.5: 制約 xi = eta、独立座標 zeta
    // 1. 改訂スパン xi = 0 -> xi = 1: eta は構文に直接変えられていないが支持 {xi, eta} で無効化錐へ入る。
    //    一方 zeta = 0 は錐外に残り、pr_W Comp(P_1) = pr_W Comp(P_2) とプローブ zeta == 0 が不変。
    let span_spec = RevisionTaskSpec {
        name: "ex_19_5_span".into(),
        kind: RevisionKind::Span,
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
                id: "zeta".into(),
                domain_values: vec![ScalarLit::int(0), ScalarLit::int(1)],
            },
        ],
        shared_constraints: vec![RevisionConstraintSpec {
            id: "c_xi_eta".into(),
            support: vec!["xi".into(), "eta".into()],
            predicate: RevisionPredicate::Equality("xi".into(), "eta".into()),
        }],
        before: RevisionSideSpec {
            assignments: BTreeMap::from([
                ("xi".into(), ScalarLit::int(0)),
                ("zeta".into(), ScalarLit::int(0)),
            ]),
            extra_constraints: vec![],
        },
        after: RevisionSideSpec {
            assignments: BTreeMap::from([
                ("xi".into(), ScalarLit::int(1)),
                ("zeta".into(), ScalarLit::int(0)),
            ]),
            extra_constraints: vec![],
        },
        explicit_delta_coords: vec![],
        probes: vec![
            RevisionEvalProbe {
                name: "eta_zero".into(),
                support: vec!["eta".into()],
                target_coord: "eta".into(),
                expected_value: ScalarLit::int(0),
                antecedent_coord: None,
                antecedent_value: None,
            },
            RevisionEvalProbe {
                name: "zeta_zero".into(),
                support: vec!["zeta".into()],
                target_coord: "zeta".into(),
                expected_value: ScalarLit::int(0),
                antecedent_coord: None,
                antecedent_value: None,
            },
        ],
        snf_spec: None,
        max_completions: 64,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };

    let out = solve_revision_task(&validate_revision_task(span_spec.clone()).unwrap());
    assert_eq!(out.verdict, Verdict::Established);
    let rev = out.revision.unwrap();
    assert!(rev.before_consistent && rev.after_consistent);
    assert!(!rev.monotonicity_applicable);
    assert!(rev.monotonicity_preserved.is_none());
    assert_eq!(rev.delta_coords, vec!["xi".to_owned()]);
    assert_eq!(
        rev.invalidation_cone,
        vec!["eta".to_owned(), "xi".to_owned()]
    );
    assert_eq!(rev.outside_cone_coords, vec!["zeta".to_owned()]);
    assert_eq!(rev.outside_projection_equal, Some(true));
    assert!(!rev.probe_results[0].outside_cone);
    assert_eq!(rev.probe_results[0].before_eval, "true");
    assert_eq!(rev.probe_results[0].after_eval, "false");
    assert!(rev.probe_results[1].outside_cone);
    assert!(rev.probe_results[1].invariant_satisfied);

    // 2. 例 19.5 後半: xi=0 のまま xi=1 相当（eta=1 を追記）で不整合になると
    //    空補完になり、定理 19.2・定理 19.4 は適用不能（outside_projection_equal=None）
    let mut bad_ext = span_spec;
    bad_ext.kind = RevisionKind::Extension;
    bad_ext.after.assignments = BTreeMap::from([
        ("xi".into(), ScalarLit::int(0)),
        ("eta".into(), ScalarLit::int(1)),
        ("zeta".into(), ScalarLit::int(0)),
    ]);
    let bad_out = solve_revision_task(&validate_revision_task(bad_ext).unwrap());
    assert_eq!(bad_out.verdict, Verdict::Refuted);
    let bad_rev = bad_out.revision.unwrap();
    assert!(!bad_rev.after_consistent);
    assert!(!bad_rev.monotonicity_applicable);
    assert!(bad_rev.monotonicity_preserved.is_none());
    assert!(bad_rev.outside_projection_equal.is_none());
}

#[test]
fn ch19_prop19_2_conditional_extension_and_non_inclusion_rejection() {
    // 非空追記で無条件・条件付きプローブが単調保存される（適用可能前件が保たれる）
    let ext = RevisionTaskSpec {
        name: "prop19_2_cond_ext".into(),
        kind: RevisionKind::Extension,
        coeff_domain: CoeffDomain::Z,
        coords: vec![
            RevisionCoordSpec {
                id: "mode".into(),
                domain_values: vec![ScalarLit::int(0), ScalarLit::int(1)],
            },
            RevisionCoordSpec {
                id: "val".into(),
                domain_values: vec![ScalarLit::int(0), ScalarLit::int(1)],
            },
        ],
        shared_constraints: vec![],
        before: RevisionSideSpec {
            assignments: BTreeMap::from([("mode".into(), ScalarLit::int(1))]),
            extra_constraints: vec![RevisionConstraintSpec {
                id: "mode_val_eq".into(),
                support: vec!["mode".into(), "val".into()],
                predicate: RevisionPredicate::Equality("mode".into(), "val".into()),
            }],
        },
        after: RevisionSideSpec {
            assignments: BTreeMap::from([
                ("mode".into(), ScalarLit::int(1)),
                ("val".into(), ScalarLit::int(1)),
            ]),
            extra_constraints: vec![RevisionConstraintSpec {
                id: "mode_val_eq".into(),
                support: vec!["mode".into(), "val".into()],
                predicate: RevisionPredicate::Equality("mode".into(), "val".into()),
            }],
        },
        explicit_delta_coords: vec![],
        probes: vec![RevisionEvalProbe {
            name: "cond_val".into(),
            support: vec!["mode".into(), "val".into()],
            target_coord: "val".into(),
            expected_value: ScalarLit::int(1),
            antecedent_coord: Some("mode".into()),
            antecedent_value: Some(ScalarLit::int(1)),
        }],
        snf_spec: None,
        max_completions: 16,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    let out = solve_revision_task(&validate_revision_task(ext.clone()).unwrap());
    assert_eq!(out.verdict, Verdict::Established);
    let rev = out.revision.unwrap();
    assert!(rev.monotonicity_applicable);
    assert_eq!(rev.monotonicity_preserved, Some(true));
    assert_eq!(rev.probe_results[0].before_eval, "applicable:true");
    assert_eq!(rev.probe_results[0].after_eval, "applicable:true");

    // Extension なのに P_1 内の記録を差し替えると ApplicabilityConditionNotMet
    let mut not_included = ext;
    not_included
        .after
        .assignments
        .insert("mode".into(), ScalarLit::int(0));
    assert!(matches!(
        solve_revision_task(&validate_revision_task(not_included).unwrap()).verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { .. })
    ));
}

#[test]
fn ch19_theorem19_7_snf_reuse_z_q_origin_only_and_rejections() {
    let mk_snf_task = |domain: CoeffDomain,
                       m_b: Vec<Vec<ScalarLit>>,
                       m_a: Vec<Vec<ScalarLit>>,
                       r_b: Vec<ScalarLit>,
                       r_a: Vec<ScalarLit>,
                       op_in_common: bool,
                       op_uniq: bool,
                       force_reuse: bool,
                       origin_only: bool| {
        RevisionTaskSpec {
            name: "snf_rev".into(),
            kind: RevisionKind::Span,
            coeff_domain: domain.clone(),
            coords: vec![],
            shared_constraints: vec![],
            before: RevisionSideSpec {
                assignments: BTreeMap::new(),
                extra_constraints: vec![],
            },
            after: RevisionSideSpec {
                assignments: BTreeMap::new(),
                extra_constraints: vec![],
            },
            explicit_delta_coords: vec![],
            probes: vec![],
            snf_spec: Some(SnfRevisionSpec {
                coeff_domain: domain,
                m_before: m_b,
                m_after: m_a,
                num_cols: 1,
                rhs_before: r_b,
                rhs_after: r_a,
                op_in_common_p0: op_in_common,
                op_uniquely_determined: op_uniq,
                force_reuse_existing_snf: force_reuse,
                origin_label_only: origin_only,
            }),
            max_completions: 16,
            provenance: prov(),
            undeclared_unobserved_slots: vec![],
        }
    };

    // 1. Z 上 2p = b: b=2 -> b=4 (解 p=2 復元, UMV=D 検算), 次に b=2 -> b=3 (不能・証拠行付)
    let z_ok = solve_revision_task(
        &validate_revision_task(mk_snf_task(
            CoeffDomain::Z,
            vec![vec![ScalarLit::int(2)]],
            vec![vec![ScalarLit::int(2)]],
            vec![ScalarLit::int(2)],
            vec![ScalarLit::int(4)],
            true,
            true,
            true,
            false,
        ))
        .unwrap(),
    );
    assert_eq!(z_ok.verdict, Verdict::Established);
    let snf_ok = z_ok.revision.unwrap().snf_reuse.unwrap();
    assert!(snf_ok.umv_verified);
    assert!(snf_ok.reused_snf);
    assert!(snf_ok.after_solvable);
    assert_eq!(snf_ok.after_particular, Some(vec!["2".to_owned()]));
    assert_eq!(snf_ok.cokernel_torsion, vec!["Z/2Z".to_owned()]);
    assert!(snf_ok.reeval.matched);

    let z_bad = solve_revision_task(
        &validate_revision_task(mk_snf_task(
            CoeffDomain::Z,
            vec![vec![ScalarLit::int(2)]],
            vec![vec![ScalarLit::int(2)]],
            vec![ScalarLit::int(2)],
            vec![ScalarLit::int(3)],
            true,
            true,
            true,
            false,
        ))
        .unwrap(),
    );
    assert_eq!(z_bad.verdict, Verdict::Refuted);
    let snf_bad = z_bad.revision.unwrap().snf_reuse.unwrap();
    assert!(snf_bad.umv_verified && snf_bad.reused_snf && !snf_bad.after_solvable);
    assert_eq!(snf_bad.inconsistency_cert_row, Some(0));
    assert!(snf_bad.reeval.matched);

    // 2. Q 上 2p = 3 (再利用) および由来ラベルのみ改訂
    let q_ok = solve_revision_task(
        &validate_revision_task(mk_snf_task(
            CoeffDomain::Q,
            vec![vec![ScalarLit::rat(2, 1).unwrap()]],
            vec![vec![ScalarLit::rat(4, 2).unwrap()]],
            vec![ScalarLit::rat(3, 1).unwrap()],
            vec![ScalarLit::rat(3, 1).unwrap()],
            true,
            true,
            true,
            true,
        ))
        .unwrap(),
    );
    assert_eq!(q_ok.verdict, Verdict::Established);
    let snf_q = q_ok.revision.unwrap().snf_reuse.unwrap();
    assert!(snf_q.reused_snf && snf_q.after_solvable && snf_q.reeval.matched);
    assert_eq!(snf_q.after_particular, Some(vec!["3/2".to_owned()]));

    // 3. 作用素変化時に force_reuse_existing_snf=true なら OperatorRevisionReuseRejected
    let reuse_rej = solve_revision_task(
        &validate_revision_task(mk_snf_task(
            CoeffDomain::Z,
            vec![vec![ScalarLit::int(2)]],
            vec![vec![ScalarLit::int(3)]],
            vec![ScalarLit::int(2)],
            vec![ScalarLit::int(6)],
            false,
            true,
            true,
            false,
        ))
        .unwrap(),
    );
    assert!(matches!(
        reuse_rej.verdict,
        Verdict::Undetermined(SilenceReason::OperatorRevisionReuseRejected { .. })
    ));

    // 4. !op_uniquely_determined なら OperatorNotUniquelyDetermined
    let not_uniq = solve_revision_task(
        &validate_revision_task(mk_snf_task(
            CoeffDomain::Z,
            vec![vec![ScalarLit::int(2)]],
            vec![vec![ScalarLit::int(2)]],
            vec![ScalarLit::int(2)],
            vec![ScalarLit::int(4)],
            false,
            false,
            false,
            false,
        ))
        .unwrap(),
    );
    assert!(matches!(
        not_uniq.verdict,
        Verdict::Undetermined(SilenceReason::OperatorNotUniquelyDetermined { .. })
    ));

    // 5. 未宣言欠測スロットで UnobservedDependency
    let mut unobs = mk_snf_task(
        CoeffDomain::Z,
        vec![vec![ScalarLit::int(1)]],
        vec![vec![ScalarLit::int(1)]],
        vec![ScalarLit::int(1)],
        vec![ScalarLit::int(1)],
        true,
        true,
        false,
        false,
    );
    unobs.undeclared_unobserved_slots = vec!["unobs_s".into()];
    assert!(matches!(
        solve_revision_task(&validate_revision_task(unobs).unwrap()).verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { .. })
    ));

    // 6. force_reuse_existing_snf = false かつ作用素変更時は m_after で再計算し reused_snf = false
    let recompute_op = solve_revision_task(
        &validate_revision_task(mk_snf_task(
            CoeffDomain::Z,
            vec![vec![ScalarLit::int(2)]],
            vec![vec![ScalarLit::int(3)]],
            vec![ScalarLit::int(2)],
            vec![ScalarLit::int(6)],
            false,
            true,
            false,
            false,
        ))
        .unwrap(),
    );
    assert_eq!(recompute_op.verdict, Verdict::Established);
    let rec_snf = recompute_op.revision.unwrap().snf_reuse.unwrap();
    assert!(!rec_snf.reused_snf);
    assert!(rec_snf.after_solvable && rec_snf.reeval.matched);
    assert_eq!(rec_snf.after_particular, Some(vec!["2".to_owned()]));

    // 7. F_p ドメイン + AllowedTuples + max_completions 超過境界
    let p5 = num_bigint::BigUint::from(5u32);
    let fp = |v: i64| ScalarLit::fp(num_bigint::BigInt::from(v), p5.clone()).unwrap();
    let fp_tuples = RevisionTaskSpec {
        name: "fp_allowed_tuples".into(),
        kind: RevisionKind::Extension,
        coeff_domain: CoeffDomain::Fp(p5.clone()),
        coords: vec![
            RevisionCoordSpec {
                id: "a".into(),
                domain_values: vec![fp(1), fp(6)],
            },
            RevisionCoordSpec {
                id: "b".into(),
                domain_values: vec![fp(2), fp(3)],
            },
        ],
        shared_constraints: vec![RevisionConstraintSpec {
            id: "allow".into(),
            support: vec!["a".into(), "b".into()],
            predicate: RevisionPredicate::AllowedTuples {
                coords: vec!["a".into(), "b".into()],
                tuples: vec![vec![fp(1), fp(2)]],
            },
        }],
        before: RevisionSideSpec {
            assignments: BTreeMap::from([("a".into(), fp(6))]),
            extra_constraints: vec![],
        },
        after: RevisionSideSpec {
            assignments: BTreeMap::from([("a".into(), fp(1)), ("b".into(), fp(2))]),
            extra_constraints: vec![],
        },
        explicit_delta_coords: vec![],
        probes: vec![],
        snf_spec: None,
        max_completions: 8,
        provenance: prov(),
        undeclared_unobserved_slots: vec![],
    };
    let fp_out = solve_revision_task(&validate_revision_task(fp_tuples.clone()).unwrap());
    assert_eq!(fp_out.verdict, Verdict::Established);
    let fp_rev = fp_out.revision.unwrap();
    // 6 mod 5 == 1 mod 5 が正規化一致するため delta_coords は ["b"] のみ
    assert_eq!(fp_rev.delta_coords, vec!["b".to_owned()]);
    assert!(fp_rev.monotonicity_applicable && fp_rev.monotonicity_preserved == Some(true));

    let mut fp_bounded = fp_tuples;
    fp_bounded.max_completions = 1;
    fp_bounded.shared_constraints.clear();
    fp_bounded.before.assignments.clear();
    fp_bounded.after.assignments.clear();
    assert!(matches!(
        solve_revision_task(&validate_revision_task(fp_bounded).unwrap()).verdict,
        Verdict::Undetermined(SilenceReason::FiniteEnumerationOutOfScope { .. })
    ));
}
