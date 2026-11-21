use super::*;
use crate::ir::change::{
    ChangeSpec, EditableTarget, EvalCondition, FixedTarget, NamedPoly, ParamDecl, PointDomain,
};
use crate::ir::presentation::{
    ComparisonPair, CoordDecl, LawKind, ObservationDecl, OperationDecl, PhaseDecl, Presentation,
    SortDecl, StateComparison, StateLaw, TranslatedStep, TranslatedWord, WordTranslation,
};
use crate::ir::provenance::{OriginKind, Provenance, SourceRef};
use crate::ir::result::Verdict;
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::ir::validate::CheckedShigureTask;
use std::collections::BTreeMap;

pub(super) fn q_lit(n: i64) -> PolyExpr {
    PolyExpr::rat(n, 1).expect("valid integer rational")
}

pub(super) fn origin(id: &str, kind: OriginKind) -> SourceRef {
    SourceRef::new(id, kind)
}

pub(super) fn single_ledger_before(domain: CoeffDomain) -> Presentation {
    Presentation {
        name: "SingleLedger".to_owned(),
        coeff_domain: domain.clone(),
        sorts: vec![SortDecl {
            name: "D".to_owned(),
            rank: 1,
            coeff_domain: domain,
            provenance: Some(origin("def:D", OriginKind::HumanAdopted)),
        }],
        phases: vec![PhaseDecl {
            name: "Active".to_owned(),
            coords: vec![CoordDecl::symbolic("x", "D")],
            state_laws: vec![],
            provenance: Some(origin("law:Active", OriginKind::HumanAdopted)),
        }],
        operations: vec![OperationDecl {
            name: "apply".to_owned(),
            source_phase: "Active".to_owned(),
            target_phase: "Active".to_owned(),
            args: vec![("u".to_owned(), "D".to_owned())],
            updates: BTreeMap::from([("x".to_owned(), PolyExpr::state("x") + PolyExpr::arg("u"))]),
            provenance: Some(origin("map:before_apply", OriginKind::StaticAnalysis)),
        }],
        observations: vec![ObservationDecl {
            name: "read".to_owned(),
            phase: "Active".to_owned(),
            components: vec![PolyExpr::state("x")],
            provenance: Some(origin("law:before_read", OriginKind::HumanAdopted)),
        }],
        provenance: Provenance::new(
            vec![origin("pres:before", OriginKind::HumanAdopted)],
            vec![],
        ),
    }
}

/// G-140 P1: 単一台帳 -> base+delta 原子操作（係数 a, b, c, d, r, s）。
fn build_ledger_p1_task(eval_cond: Option<EvalCondition>) -> CheckedShigureTask {
    let before = single_ledger_before(CoeffDomain::Q);
    let after = Presentation {
        name: "SplitLedgerP1".to_owned(),
        coeff_domain: CoeffDomain::Q,
        sorts: vec![SortDecl {
            name: "D".to_owned(),
            rank: 1,
            coeff_domain: CoeffDomain::Q,
            provenance: None,
        }],
        phases: vec![PhaseDecl {
            name: "Split".to_owned(),
            coords: vec![CoordDecl::symbolic("B", "D"), CoordDecl::symbolic("C", "D")],
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![
            OperationDecl {
                name: "apply".to_owned(),
                source_phase: "Split".to_owned(),
                target_phase: "Split".to_owned(),
                args: vec![("u".to_owned(), "D".to_owned())],
                updates: BTreeMap::from([
                    (
                        "B".to_owned(),
                        PolyExpr::state("B") + PolyExpr::param("c") * PolyExpr::arg("u"),
                    ),
                    (
                        "C".to_owned(),
                        PolyExpr::state("C") + PolyExpr::param("d") * PolyExpr::arg("u"),
                    ),
                ]),
                provenance: Some(origin("map:after_apply", OriginKind::StaticAnalysis)),
            },
            OperationDecl {
                name: "compact".to_owned(),
                source_phase: "Split".to_owned(),
                target_phase: "Split".to_owned(),
                args: vec![("t".to_owned(), "D".to_owned())],
                updates: BTreeMap::from([
                    (
                        "B".to_owned(),
                        PolyExpr::state("B") + PolyExpr::param("r") * PolyExpr::arg("t"),
                    ),
                    (
                        "C".to_owned(),
                        PolyExpr::state("C") + PolyExpr::param("s") * PolyExpr::arg("t"),
                    ),
                ]),
                provenance: Some(origin("map:after_compact", OriginKind::RuntimeObservation)),
            },
        ],
        observations: vec![ObservationDecl {
            name: "read".to_owned(),
            phase: "Split".to_owned(),
            components: vec![
                PolyExpr::param("a") * PolyExpr::state("B")
                    + PolyExpr::param("b") * PolyExpr::state("C"),
            ],
            provenance: None,
        }],
        provenance: Provenance::new(
            vec![origin("pres:p1_after", OriginKind::LlmCandidate)],
            vec![],
        ),
    };

    let pair = ComparisonPair {
        before,
        after,
        state_comparisons: vec![StateComparison {
            after_phase: "Split".to_owned(),
            before_phase: "Active".to_owned(),
            map: BTreeMap::from([(
                "x".to_owned(),
                PolyExpr::param("a") * PolyExpr::state("B")
                    + PolyExpr::param("b") * PolyExpr::state("C"),
            )]),
            provenance: None,
        }],
        word_translation: WordTranslation {
            entries: vec![
                TranslatedWord {
                    after_operation: "apply".to_owned(),
                    steps: vec![TranslatedStep {
                        before_operation: "apply".to_owned(),
                        arg_exprs: vec![PolyExpr::arg("u")],
                    }],
                    provenance: None,
                },
                TranslatedWord {
                    after_operation: "compact".to_owned(),
                    steps: vec![],
                    provenance: None,
                },
            ],
        },
    };

    let params: Vec<ParamDecl> = ["a", "b", "c", "d", "r", "s"]
        .into_iter()
        .map(|name| ParamDecl {
            name: name.to_owned(),
            coeff_domain: CoeffDomain::Q,
            provenance: None,
        })
        .collect();

    let change_spec = ChangeSpec {
        name: "H_p1".to_owned(),
        coeff_domain: CoeffDomain::Q,
        parameters: params,
        fixed: vec![FixedTarget::ObservationExpr {
            presentation: "SingleLedger".to_owned(),
            phase: "Active".to_owned(),
            observation: "read".to_owned(),
        }],
        editable: vec![
            EditableTarget::OperationExpr {
                presentation: "SplitLedgerP1".to_owned(),
                operation: "apply".to_owned(),
            },
            EditableTarget::OperationExpr {
                presentation: "SplitLedgerP1".to_owned(),
                operation: "compact".to_owned(),
            },
            EditableTarget::StateComparisonExpr {
                after_phase: "Split".to_owned(),
            },
        ],
        provenance: Provenance::new(vec![origin("law:H_p1", OriginKind::HumanAdopted)], vec![]),
    };

    CheckedShigureTask::validate(pair, change_spec, eval_cond).expect("valid P1 task")
}

/// G-140 P3 / P5 / P6: 2-phase snapshot 台帳移行（`with_rho`: P5/P6(c)/(d) 用、`fix_old_busy_law`: P6(d) 対照）。
pub(super) fn build_ledger_snapshot_task(
    with_rho: bool,
    fix_old_busy_law: bool,
    eval_cond: Option<EvalCondition>,
) -> CheckedShigureTask {
    let before = single_ledger_before(CoeffDomain::Q);
    let delta = PolyExpr::param("delta");
    let mu = PolyExpr::param("mu");
    let rho = PolyExpr::param("rho");

    let busy_law_poly = if with_rho && !fix_old_busy_law {
        mu.clone() * (q_lit(1) - rho.clone()) * (PolyExpr::state("h") - PolyExpr::state("C"))
    } else {
        mu.clone() * (PolyExpr::state("h") - PolyExpr::state("C"))
    };

    let finish_c = if with_rho {
        PolyExpr::state("C")
            - mu.clone()
                * ((q_lit(1) - rho.clone()) * PolyExpr::state("C") + rho * PolyExpr::state("h"))
    } else {
        (q_lit(1) - mu.clone()) * PolyExpr::state("C")
    };

    let after = Presentation {
        name: "SnapshotLedger".to_owned(),
        coeff_domain: CoeffDomain::Q,
        sorts: vec![SortDecl {
            name: "D".to_owned(),
            rank: 1,
            coeff_domain: CoeffDomain::Q,
            provenance: None,
        }],
        phases: vec![
            PhaseDecl {
                name: "Idle".to_owned(),
                coords: vec![CoordDecl::symbolic("B", "D"), CoordDecl::symbolic("C", "D")],
                state_laws: vec![],
                provenance: None,
            },
            PhaseDecl {
                name: "Busy".to_owned(),
                coords: vec![
                    CoordDecl::symbolic("B", "D"),
                    CoordDecl::symbolic("C", "D"),
                    CoordDecl::symbolic("h", "D"),
                ],
                state_laws: vec![StateLaw {
                    name: "busy_law".to_owned(),
                    kind: LawKind::Representation,
                    polynomial: busy_law_poly,
                    provenance: Some(origin("law:busy_law", OriginKind::HumanAdopted)),
                }],
                provenance: None,
            },
        ],
        operations: vec![
            OperationDecl {
                name: "begin".to_owned(),
                source_phase: "Idle".to_owned(),
                target_phase: "Busy".to_owned(),
                args: vec![],
                updates: BTreeMap::from([
                    ("B".to_owned(), PolyExpr::state("B")),
                    ("C".to_owned(), PolyExpr::state("C")),
                    ("h".to_owned(), PolyExpr::state("C")),
                ]),
                provenance: None,
            },
            OperationDecl {
                name: "apply_idle".to_owned(),
                source_phase: "Idle".to_owned(),
                target_phase: "Idle".to_owned(),
                args: vec![("u".to_owned(), "D".to_owned())],
                updates: BTreeMap::from([
                    (
                        "B".to_owned(),
                        PolyExpr::state("B") + (q_lit(1) - delta.clone()) * PolyExpr::arg("u"),
                    ),
                    (
                        "C".to_owned(),
                        PolyExpr::state("C") + delta.clone() * PolyExpr::arg("u"),
                    ),
                ]),
                provenance: None,
            },
            OperationDecl {
                name: "apply_busy".to_owned(),
                source_phase: "Busy".to_owned(),
                target_phase: "Busy".to_owned(),
                args: vec![("u".to_owned(), "D".to_owned())],
                updates: BTreeMap::from([
                    (
                        "B".to_owned(),
                        PolyExpr::state("B") + (q_lit(1) - delta.clone()) * PolyExpr::arg("u"),
                    ),
                    (
                        "C".to_owned(),
                        PolyExpr::state("C") + delta * PolyExpr::arg("u"),
                    ),
                    ("h".to_owned(), PolyExpr::state("h")),
                ]),
                provenance: None,
            },
            OperationDecl {
                name: "finish".to_owned(),
                source_phase: "Busy".to_owned(),
                target_phase: "Idle".to_owned(),
                args: vec![],
                updates: BTreeMap::from([
                    (
                        "B".to_owned(),
                        PolyExpr::state("B") + mu * PolyExpr::state("h"),
                    ),
                    ("C".to_owned(), finish_c),
                ]),
                provenance: None,
            },
        ],
        observations: vec![
            ObservationDecl {
                name: "read".to_owned(),
                phase: "Idle".to_owned(),
                components: vec![PolyExpr::state("B") + PolyExpr::state("C")],
                provenance: None,
            },
            ObservationDecl {
                name: "read".to_owned(),
                phase: "Busy".to_owned(),
                components: vec![PolyExpr::state("B") + PolyExpr::state("C")],
                provenance: None,
            },
        ],
        provenance: Provenance::new(
            vec![origin("pres:snapshot_after", OriginKind::StaticAnalysis)],
            vec![],
        ),
    };

    let pair = ComparisonPair {
        before,
        after,
        state_comparisons: vec![
            StateComparison {
                after_phase: "Idle".to_owned(),
                before_phase: "Active".to_owned(),
                map: BTreeMap::from([(
                    "x".to_owned(),
                    PolyExpr::state("B") + PolyExpr::state("C"),
                )]),
                provenance: None,
            },
            StateComparison {
                after_phase: "Busy".to_owned(),
                before_phase: "Active".to_owned(),
                map: BTreeMap::from([(
                    "x".to_owned(),
                    PolyExpr::state("B") + PolyExpr::state("C"),
                )]),
                provenance: None,
            },
        ],
        word_translation: WordTranslation {
            entries: vec![
                TranslatedWord {
                    after_operation: "begin".to_owned(),
                    steps: vec![],
                    provenance: None,
                },
                TranslatedWord {
                    after_operation: "apply_idle".to_owned(),
                    steps: vec![TranslatedStep {
                        before_operation: "apply".to_owned(),
                        arg_exprs: vec![PolyExpr::arg("u")],
                    }],
                    provenance: None,
                },
                TranslatedWord {
                    after_operation: "apply_busy".to_owned(),
                    steps: vec![TranslatedStep {
                        before_operation: "apply".to_owned(),
                        arg_exprs: vec![PolyExpr::arg("u")],
                    }],
                    provenance: None,
                },
                TranslatedWord {
                    after_operation: "finish".to_owned(),
                    steps: vec![],
                    provenance: None,
                },
            ],
        },
    };

    let mut params = vec![
        ParamDecl {
            name: "delta".to_owned(),
            coeff_domain: CoeffDomain::Q,
            provenance: None,
        },
        ParamDecl {
            name: "mu".to_owned(),
            coeff_domain: CoeffDomain::Q,
            provenance: None,
        },
    ];
    if with_rho {
        params.push(ParamDecl {
            name: "rho".to_owned(),
            coeff_domain: CoeffDomain::Q,
            provenance: None,
        });
    }

    let mut fixed = vec![
        FixedTarget::ObservationExpr {
            presentation: "SingleLedger".to_owned(),
            phase: "Active".to_owned(),
            observation: "read".to_owned(),
        },
        FixedTarget::StateComparisonExpr {
            after_phase: "Idle".to_owned(),
        },
        FixedTarget::StateComparisonExpr {
            after_phase: "Busy".to_owned(),
        },
    ];
    let mut editable = vec![
        EditableTarget::OperationExpr {
            presentation: "SnapshotLedger".to_owned(),
            operation: "apply_idle".to_owned(),
        },
        EditableTarget::OperationExpr {
            presentation: "SnapshotLedger".to_owned(),
            operation: "apply_busy".to_owned(),
        },
        EditableTarget::OperationExpr {
            presentation: "SnapshotLedger".to_owned(),
            operation: "finish".to_owned(),
        },
    ];
    if with_rho && !fix_old_busy_law {
        editable.push(EditableTarget::RepresentationLaw {
            presentation: "SnapshotLedger".to_owned(),
            phase: "Busy".to_owned(),
            law: "busy_law".to_owned(),
        });
    } else {
        fixed.push(FixedTarget::RepresentationLaw {
            presentation: "SnapshotLedger".to_owned(),
            phase: "Busy".to_owned(),
            law: "busy_law".to_owned(),
        });
    }

    let change_spec = ChangeSpec {
        name: "H_snapshot".to_owned(),
        coeff_domain: CoeffDomain::Q,
        parameters: params,
        fixed,
        editable,
        provenance: Provenance::new(vec![origin("law:H_snap", OriginKind::HumanAdopted)], vec![]),
    };

    CheckedShigureTask::validate(pair, change_spec, eval_cond).expect("valid snapshot task")
}

/// 単一パラメータ多項式方程式を直接生む一般の 1-phase テストタスク構築ヘルパー。
pub(super) fn build_single_param_residual_task(
    domain: CoeffDomain,
    param_name: &str,
    residual_poly: PolyExpr,
    eval_cond: Option<EvalCondition>,
) -> CheckedShigureTask {
    let before = single_ledger_before(domain.clone());
    let after = Presentation {
        name: "ParamAfter".to_owned(),
        coeff_domain: domain.clone(),
        sorts: vec![SortDecl {
            name: "D".to_owned(),
            rank: 1,
            coeff_domain: domain.clone(),
            provenance: None,
        }],
        phases: vec![PhaseDecl {
            name: "Active".to_owned(),
            coords: vec![CoordDecl::symbolic("x", "D")],
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "apply".to_owned(),
            source_phase: "Active".to_owned(),
            target_phase: "Active".to_owned(),
            args: vec![("u".to_owned(), "D".to_owned())],
            updates: BTreeMap::from([(
                "x".to_owned(),
                PolyExpr::state("x") + PolyExpr::arg("u") + residual_poly,
            )]),
            provenance: None,
        }],
        observations: vec![ObservationDecl {
            name: "read".to_owned(),
            phase: "Active".to_owned(),
            components: vec![PolyExpr::state("x")],
            provenance: None,
        }],
        provenance: Provenance::default(),
    };
    let pair = ComparisonPair {
        before,
        after,
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
    let change_spec = ChangeSpec {
        name: "H_single".to_owned(),
        coeff_domain: domain.clone(),
        parameters: vec![ParamDecl {
            name: param_name.to_owned(),
            coeff_domain: domain,
            provenance: None,
        }],
        fixed: vec![],
        editable: vec![EditableTarget::OperationExpr {
            presentation: "ParamAfter".to_owned(),
            operation: "apply".to_owned(),
        }],
        provenance: Provenance::default(),
    };
    CheckedShigureTask::validate(pair, change_spec, eval_cond).expect("valid single-param task")
}

#[test]
fn ac3_a_ledger_p1_atomic_preservation_and_marked_fiber_restoration() {
    // 1. 全係数の保存方程式: (a*c + b*d - 1, a*r + b*s) の簡約 Grevlex Gröbner 基底
    //    （原始 2 式に加え G-140 P1.1 の syzygy 関係 b*(d*r - c*s) - r = 0 を含む）。
    let task_full = build_ledger_p1_task(None);
    let out_full = execute_shigure_task(&task_full, ShigureQueryKind::SemanticPreservation);
    assert_eq!(out_full.verdict, Verdict::Established);
    assert_eq!(out_full.residual_ideal.len(), 3);
    assert!(
        out_full
            .residual_ideal
            .contains(&"a*c + b*d - 1".to_owned())
    );
    assert!(out_full.residual_ideal.contains(&"a*r + b*s".to_owned()));
    assert!(
        out_full
            .residual_ideal
            .contains(&"b*c*s - b*d*r + r".to_owned())
            || out_full
                .residual_ideal
                .contains(&"b*d*r - b*c*s - r".to_owned())
    );
    // 由来種別（StaticAnalysis, RuntimeObservation, LlmCandidate, HumanAdopted）がすべて保持される。
    let kinds: Vec<OriginKind> = out_full.provenance.origins.iter().map(|o| o.kind).collect();
    assert!(kinds.contains(&OriginKind::StaticAnalysis));
    assert!(kinds.contains(&OriginKind::RuntimeObservation));
    assert!(kinds.contains(&OriginKind::LlmCandidate));
    assert!(kinds.contains(&OriginKind::HumanAdopted));

    // 2. marked fiber p = (1, 1) の評価条件 V(a - 1, b - 1) から操作式・h・τ を復元し再評価一致。
    let marked_cond = EvalCondition {
        name: "marked_fiber_p_1_1".to_owned(),
        evaluations: vec![
            NamedPoly::new("p_B", PolyExpr::param("a")),
            NamedPoly::new("p_C", PolyExpr::param("b")),
        ],
        equations: vec![
            NamedPoly::new("a_eq_1", PolyExpr::param("a") - q_lit(1)),
            NamedPoly::new("b_eq_1", PolyExpr::param("b") - q_lit(1)),
        ],
        invertibles: vec![],
        point_domain: PointDomain::RationalPoints,
        provenance: Provenance::default(),
    };
    let task_marked = build_ledger_p1_task(Some(marked_cond));
    let out_marked = execute_shigure_task(&task_marked, ShigureQueryKind::ConditionalSolutionSpace);
    assert_eq!(out_marked.verdict, Verdict::Established);
    let restored = out_marked.restored.expect("marked fiber must be restored");
    assert!(restored.reeval.checked && restored.reeval.matched);
    assert_eq!(
        restored.parameter_assignments.get("a").map(String::as_str),
        Some("1")
    );
    assert_eq!(
        restored.parameter_assignments.get("b").map(String::as_str),
        Some("1")
    );
    assert_eq!(
        restored.free_parameters,
        vec!["d".to_owned(), "s".to_owned()]
    );
    assert_eq!(restored.state_comparisons["Split"]["x"], "B + C");
    assert_eq!(restored.word_translation["apply"], vec!["apply(u)"]);
    assert!(restored.word_translation["compact"].is_empty());
}

#[test]
fn ac3_b_ledger_p3_p6_snapshot_family_and_open_conditions() {
    // 1. P3: 非線形保存族 V(mu*delta) を商環閉性から導出（ambient mu=0 へ強めない）。
    let task_p3 = build_ledger_snapshot_task(false, true, None);
    let out_p3 = execute_shigure_task(&task_p3, ShigureQueryKind::SemanticPreservation);
    assert_eq!(out_p3.verdict, Verdict::Established);
    assert_eq!(out_p3.residual_ideal, vec!["delta*mu".to_owned()]);

    // 2. D(mu) => delta = 0 強制。
    let cond_d_mu = EvalCondition {
        name: "D_mu".to_owned(),
        evaluations: vec![NamedPoly::new("mu", PolyExpr::param("mu"))],
        equations: vec![],
        invertibles: vec![NamedPoly::new("mu_unit", PolyExpr::param("mu"))],
        point_domain: PointDomain::AlgebraicClosure,
        provenance: Provenance::default(),
    };
    let out_d_mu = execute_shigure_task(
        &build_ledger_snapshot_task(false, true, Some(cond_d_mu)),
        ShigureQueryKind::ConditionalSolutionSpace,
    );
    assert_eq!(out_d_mu.verdict, Verdict::Established);
    assert_eq!(out_d_mu.residual_ideal, vec!["delta".to_owned()]);
    let rest_mu = out_d_mu.restored.expect("restored under D(mu)");
    assert_eq!(rest_mu.parameter_assignments["delta"], "0");
    assert_eq!(rest_mu.free_parameters, vec!["mu".to_owned()]);
    assert_eq!(rest_mu.operations["apply_busy"]["C"], "C");
    assert!(rest_mu.reeval.checked && rest_mu.reeval.matched);

    // 3. D(delta) => mu = 0 強制。
    let cond_d_delta = EvalCondition {
        name: "D_delta".to_owned(),
        evaluations: vec![NamedPoly::new("delta", PolyExpr::param("delta"))],
        equations: vec![],
        invertibles: vec![NamedPoly::new("delta_unit", PolyExpr::param("delta"))],
        point_domain: PointDomain::AlgebraicClosure,
        provenance: Provenance::default(),
    };
    let out_d_delta = execute_shigure_task(
        &build_ledger_snapshot_task(false, true, Some(cond_d_delta)),
        ShigureQueryKind::ConditionalSolutionSpace,
    );
    assert_eq!(out_d_delta.verdict, Verdict::Established);
    assert_eq!(out_d_delta.residual_ideal, vec!["mu".to_owned()]);
    let rest_delta = out_d_delta.restored.expect("restored under D(delta)");
    assert_eq!(rest_delta.parameter_assignments["mu"], "0");
    assert_eq!(rest_delta.operations["finish"]["B"], "B");
    assert_eq!(rest_delta.operations["finish"]["C"], "C");
    assert_eq!(rest_delta.state_laws["Busy"], vec!["0".to_owned()]);
    assert!(rest_delta.reeval.checked && rest_delta.reeval.matched);

    // 4. D(mu*delta) => 空性証明 1 in I（verified = true）。
    let cond_d_both = EvalCondition {
        name: "D_mu_delta".to_owned(),
        evaluations: vec![NamedPoly::new(
            "mu_delta",
            PolyExpr::param("mu") * PolyExpr::param("delta"),
        )],
        equations: vec![],
        invertibles: vec![NamedPoly::new(
            "both_unit",
            PolyExpr::param("mu") * PolyExpr::param("delta"),
        )],
        point_domain: PointDomain::AlgebraicClosure,
        provenance: Provenance::default(),
    };
    let out_empty = execute_shigure_task(
        &build_ledger_snapshot_task(false, true, Some(cond_d_both)),
        ShigureQueryKind::ConditionalSolutionSpace,
    );
    assert_eq!(out_empty.verdict, Verdict::Refuted);
    let witness = out_empty
        .empty_witness
        .expect("verified empty witness required");
    assert!(witness.verified);
    assert!(out_empty.restored.is_none());
}

#[test]
fn ac3_c_and_d_finish_rho_restores_finish_snap_while_fixed_old_busy_law_stays_empty() {
    // AC3(c): finish_rho + 編集可能な Busy 表示 Law g_rho = mu*(1 - rho)*(h - C)。
    let task_p5 = build_ledger_snapshot_task(true, false, None);
    let out_p5 = execute_shigure_task(&task_p5, ShigureQueryKind::SemanticPreservation);
    assert_eq!(out_p5.verdict, Verdict::Established);
    assert_eq!(
        out_p5.residual_ideal,
        vec!["delta*mu*rho - delta*mu".to_owned()]
    );

    for pt_domain in [PointDomain::AlgebraicClosure, PointDomain::RationalPoints] {
        let cond = EvalCondition {
            name: "D_mu_delta".to_owned(),
            evaluations: vec![NamedPoly::new(
                "mu_delta",
                PolyExpr::param("mu") * PolyExpr::param("delta"),
            )],
            equations: vec![],
            invertibles: vec![NamedPoly::new(
                "mu_delta_unit",
                PolyExpr::param("mu") * PolyExpr::param("delta"),
            )],
            point_domain: pt_domain,
            provenance: Provenance::default(),
        };
        let out_c = execute_shigure_task(
            &build_ledger_snapshot_task(true, false, Some(cond)),
            ShigureQueryKind::ConditionalSolutionSpace,
        );
        assert_eq!(out_c.verdict, Verdict::Established);
        assert_eq!(out_c.residual_ideal, vec!["rho - 1".to_owned()]);
        let restored = out_c.restored.expect("finish_snap must be restored");
        assert_eq!(restored.parameter_assignments["rho"], "1");
        assert_eq!(
            restored.free_parameters,
            vec!["delta".to_owned(), "mu".to_owned()]
        );
        // finish_snap: (B + mu*h, C - mu*h) と全状態 Busy（Law = 0）を復元。
        assert_eq!(restored.operations["finish"]["B"], "h*mu + B");
        assert_eq!(restored.operations["finish"]["C"], "-h*mu + C");
        assert_eq!(restored.state_laws["Busy"], vec!["0".to_owned()]);
        assert_eq!(restored.state_comparisons["Idle"]["x"], "B + C");
        assert_eq!(restored.state_comparisons["Busy"]["x"], "B + C");
        assert!(restored.word_translation["begin"].is_empty());
        assert!(restored.word_translation["finish"].is_empty());
        assert_eq!(restored.word_translation["apply_busy"], vec!["apply(u)"]);
        assert!(restored.reeval.checked && restored.reeval.matched);
    }

    // AC3(d): 旧 Busy Law g = mu*(h - C) を固定した対照条件では finish_rho を許しても依然空。
    let cond_contrast = EvalCondition {
        name: "D_mu_delta_contrast".to_owned(),
        evaluations: vec![NamedPoly::new(
            "mu_delta",
            PolyExpr::param("mu") * PolyExpr::param("delta"),
        )],
        equations: vec![],
        invertibles: vec![NamedPoly::new(
            "mu_delta_unit",
            PolyExpr::param("mu") * PolyExpr::param("delta"),
        )],
        point_domain: PointDomain::AlgebraicClosure,
        provenance: Provenance::default(),
    };
    let out_d = execute_shigure_task(
        &build_ledger_snapshot_task(true, true, Some(cond_contrast)),
        ShigureQueryKind::ConditionalSolutionSpace,
    );
    assert_eq!(out_d.verdict, Verdict::Refuted);
    assert!(out_d.empty_witness.expect("empty witness").verified);
    assert!(out_d.restored.is_none());
}
