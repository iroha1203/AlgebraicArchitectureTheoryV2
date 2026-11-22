use crate::ir::change::{ChangeSpec, NamedPoly, ParamDecl};
use crate::ir::morphism::{MorphismDirection, StateMorphism};
use crate::ir::path::{
    CheckedPathTask, ModelEndpoint, OneStepRule, PathKind, PathQueryMode, PathSpec,
    ProtocolExecutionSpec,
};
use crate::ir::presentation::{
    ComparisonPair, CoordDecl, LawKind, ObservationDecl, OperationDecl, PhaseDecl, Presentation,
    SortDecl, StateComparison, StateLaw, TranslatedStep, TranslatedWord, WordTranslation,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::Verdict;
use crate::ir::result_ext::PathOutcomeKind;
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::solver::solve_path_task;
use std::collections::BTreeMap;

pub(super) fn orig(id: &str) -> SourceRef {
    SourceRef::new(id, OriginKind::HumanAdopted).with_location(
        "path-test",
        "path.law",
        Some((1, 20)),
    )
}

pub(super) fn clit(d: &CoeffDomain, n: i64) -> PolyExpr {
    match d {
        CoeffDomain::Z => PolyExpr::int(n),
        CoeffDomain::Q => PolyExpr::rat(n, 1).expect("rat"),
        CoeffDomain::Fp(m) => {
            PolyExpr::Const(ScalarLit::fp(num_bigint::BigInt::from(n), m.clone()).expect("fp"))
        }
    }
}

pub(super) fn slit(d: &CoeffDomain, n: i64) -> ScalarLit {
    match d {
        CoeffDomain::Z => ScalarLit::int(n),
        CoeffDomain::Q => ScalarLit::rat(n, 1).expect("rat"),
        CoeffDomain::Fp(m) => ScalarLit::fp(num_bigint::BigInt::from(n), m.clone()).expect("fp"),
    }
}

fn p5_ledger_pres(
    name: &str,
    domain: CoeffDomain,
    delta: PolyExpr,
    mu: PolyExpr,
    rho: PolyExpr,
) -> Presentation {
    // Idle 公開取引 transact_u = begin ; apply_u ; finish_rho の原式展開（G-140 P5 / line 278）
    let one = clit(&domain, 1);
    let b_after_apply = PolyExpr::state("B") + (one.clone() - delta.clone()) * PolyExpr::arg("u");
    let c_after_apply = PolyExpr::state("C") + delta * PolyExpr::arg("u");
    let b_next = b_after_apply + mu.clone() * PolyExpr::state("C");
    let c_next = c_after_apply.clone()
        - mu * ((one - rho.clone()) * c_after_apply + rho * PolyExpr::state("C"));
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
            name: "Idle".into(),
            coords: vec![CoordDecl::symbolic("B", "D"), CoordDecl::symbolic("C", "D")],
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "transact".into(),
            source_phase: "Idle".into(),
            target_phase: "Idle".into(),
            args: vec![("u".into(), "D".into())],
            domain_laws: vec![],
            updates: BTreeMap::from([("B".into(), b_next), ("C".into(), c_next)]),
            provenance: None,
        }],
        observations: vec![ObservationDecl {
            name: "read".into(),
            phase: "Idle".into(),
            components: vec![PolyExpr::state("B") + PolyExpr::state("C")],
            provenance: None,
        }],
        provenance: Provenance::new(vec![orig(name)], vec![MathClause::G140P5Dot1]),
    }
}

fn ledger_idle_morph(
    name: &str,
    domain: &CoeffDomain,
    first_coord: PolyExpr,
    second_coord: PolyExpr,
) -> StateMorphism {
    let bc = PolyExpr::state("B") + PolyExpr::state("C");
    let _ = domain;
    StateMorphism {
        source: name.into(),
        target: name.into(),
        state_comparisons: vec![StateComparison {
            after_phase: "Idle".into(),
            before_phase: "Idle".into(),
            map: BTreeMap::from([
                ("B".into(), first_coord * bc.clone()),
                ("C".into(), second_coord * bc),
            ]),
            provenance: None,
        }],
        word_translation: WordTranslation {
            entries: vec![TranslatedWord {
                after_operation: "transact".into(),
                steps: vec![TranslatedStep {
                    before_operation: "transact".into(),
                    arg_exprs: vec![PolyExpr::arg("u")],
                }],
                provenance: None,
            }],
        },
        provenance: None,
    }
}

#[test]
fn path_p51_ledger_four_valid_and_two_rejected_at_step2_over_q_and_z() {
    for domain in [CoeffDomain::Q, CoeffDomain::Z] {
        let pres = p5_ledger_pres(
            "L",
            domain.clone(),
            PolyExpr::param("delta"),
            PolyExpr::param("mu"),
            PolyExpr::param("rho"),
        );
        let one = clit(&domain, 1);
        let zero = clit(&domain, 0);
        let delta_morph = ledger_idle_morph("L", &domain, one.clone(), zero);
        let keep_delta_morph = ledger_idle_morph(
            "L",
            &domain,
            one - PolyExpr::param("delta"),
            PolyExpr::param("delta"),
        );
        let rules = vec![
            OneStepRule {
                name: "toggle_delta".into(),
                from_vertex: "V".into(),
                to_vertex: "V".into(),
                param_guards: vec![NamedPoly {
                    name: "d0".into(),
                    expr: PolyExpr::param("delta"),
                    provenance: None,
                }],
                param_updates: BTreeMap::from([("delta".into(), clit(&domain, 1))]),
                morphism: delta_morph,
                eval_condition: None,
                provenance: None,
            },
            OneStepRule {
                name: "toggle_mu".into(),
                from_vertex: "V".into(),
                to_vertex: "V".into(),
                param_guards: vec![NamedPoly {
                    name: "m0".into(),
                    expr: PolyExpr::param("mu"),
                    provenance: None,
                }],
                param_updates: BTreeMap::from([("mu".into(), clit(&domain, 1))]),
                morphism: keep_delta_morph.clone(),
                eval_condition: None,
                provenance: None,
            },
            OneStepRule {
                name: "toggle_rho".into(),
                from_vertex: "V".into(),
                to_vertex: "V".into(),
                param_guards: vec![NamedPoly {
                    name: "r0".into(),
                    expr: PolyExpr::param("rho"),
                    provenance: None,
                }],
                param_updates: BTreeMap::from([("rho".into(), clit(&domain, 1))]),
                morphism: keep_delta_morph,
                eval_condition: None,
                provenance: None,
            },
        ];
        let spec = PathSpec {
            name: "p51".into(),
            kind: PathKind::FixedProtocolChangePath,
            direction: MorphismDirection::TimeOrder,
            query_mode: PathQueryMode::Find,
            length: Some(3),
            vertices: BTreeMap::from([("V".into(), pres)]),
            rules,
            start: Some(ModelEndpoint {
                vertex: "V".into(),
                param_values: BTreeMap::from([
                    ("delta".into(), slit(&domain, 0)),
                    ("mu".into(), slit(&domain, 0)),
                    ("rho".into(), slit(&domain, 0)),
                ]),
            }),
            end: Some(ModelEndpoint {
                vertex: "V".into(),
                param_values: BTreeMap::from([
                    ("delta".into(), slit(&domain, 1)),
                    ("mu".into(), slit(&domain, 1)),
                    ("rho".into(), slit(&domain, 1)),
                ]),
            }),
            protocol: None,
            change_spec: ChangeSpec {
                name: "H".into(),
                coeff_domain: domain.clone(),
                parameters: vec![
                    ParamDecl {
                        name: "delta".into(),
                        coeff_domain: domain.clone(),
                        provenance: None,
                    },
                    ParamDecl {
                        name: "mu".into(),
                        coeff_domain: domain.clone(),
                        provenance: None,
                    },
                    ParamDecl {
                        name: "rho".into(),
                        coeff_domain: domain.clone(),
                        provenance: None,
                    },
                ],
                fixed: vec![],
                editable: vec![],
                provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140P5Dot1]),
            },
            eval_condition: None,
            provenance: Provenance::new(vec![orig("p51")], vec![MathClause::G140P5Dot1]),
        };

        let out = solve_path_task(&CheckedPathTask::validate(spec).unwrap());
        assert_eq!(out.verdict, Verdict::Established, "domain={domain:?}");
        let detail = out.path.unwrap();
        assert_eq!(detail.path_kind, PathOutcomeKind::FixedProtocolChangePath);
        assert_eq!(
            detail.valid_paths.len(),
            4,
            "domain={domain:?}, valid={:?}, rejected={:?}",
            detail
                .valid_paths
                .iter()
                .map(|p| &p.steps)
                .collect::<Vec<_>>(),
            detail.rejected_candidates
        );
        let mut valid_seqs: Vec<Vec<String>> =
            detail.valid_paths.iter().map(|p| p.steps.clone()).collect();
        valid_seqs.sort();
        assert_eq!(
            valid_seqs,
            vec![
                vec!["toggle_delta", "toggle_rho", "toggle_mu"],
                vec!["toggle_mu", "toggle_rho", "toggle_delta"],
                vec!["toggle_rho", "toggle_delta", "toggle_mu"],
                vec!["toggle_rho", "toggle_mu", "toggle_delta"],
            ]
        );
        for p in &detail.valid_paths {
            assert!(p.reeval.matched);
        }
        let step2_rejected: Vec<_> = detail
            .rejected_candidates
            .iter()
            .filter(|c| {
                c.steps == ["toggle_delta", "toggle_mu", "toggle_rho"]
                    || c.steps == ["toggle_mu", "toggle_delta", "toggle_rho"]
            })
            .collect();
        assert_eq!(step2_rejected.len(), 2);
        for rej in step2_rejected {
            assert_eq!(rej.failed_step, 2);
            assert_eq!(rej.intermediate_state["delta"], "1");
            assert_eq!(rej.intermediate_state["mu"], "1");
            assert_eq!(rej.intermediate_state["rho"], "0");
            assert!(
                rej.residuals.iter().any(|r| r == "1" || r == "-1"),
                "residuals={:?}",
                rej.residuals
            );
        }
    }
}

#[test]
fn path_p52_enlarged_protocol_execution_paths_and_distinct_kind() {
    let q = CoeffDomain::Q;
    let one = clit(&q, 1);
    let old = Presentation {
        name: "Old".into(),
        coeff_domain: q.clone(),
        sorts: vec![SortDecl {
            name: "D".into(),
            rank: 1,
            coeff_domain: q.clone(),
            provenance: Some(orig("d")),
        }],
        phases: vec![PhaseDecl {
            name: "Single".into(),
            coords: vec![CoordDecl::symbolic("x", "D")],
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "apply".into(),
            source_phase: "Single".into(),
            target_phase: "Single".into(),
            args: vec![("u".into(), "D".into())],
            domain_laws: vec![],
            updates: BTreeMap::from([("x".into(), PolyExpr::state("x") + PolyExpr::arg("u"))]),
            provenance: None,
        }],
        observations: vec![ObservationDecl {
            name: "read".into(),
            phase: "Single".into(),
            components: vec![PolyExpr::state("x")],
            provenance: None,
        }],
        provenance: Provenance::new(vec![orig("old")], vec![MathClause::G140P5Dot2]),
    };

    let d = PolyExpr::state("delta");
    let m = PolyExpr::state("mu");
    let r = PolyExpr::state("rho");
    let f = m.clone() * d.clone() * (one.clone() - r.clone());
    let g_rho =
        m.clone() * (one.clone() - r.clone()) * (PolyExpr::state("h") - PolyExpr::state("C"));
    let finish_c = PolyExpr::state("C")
        - m.clone()
            * ((one.clone() - r.clone()) * PolyExpr::state("C") + r.clone() * PolyExpr::state("h"));
    let after = Presentation {
        name: "Enlarged".into(),
        coeff_domain: q.clone(),
        sorts: vec![SortDecl {
            name: "D".into(),
            rank: 1,
            coeff_domain: q.clone(),
            provenance: Some(orig("d")),
        }],
        phases: vec![
            PhaseDecl {
                name: "Idle".into(),
                coords: vec![
                    CoordDecl::symbolic("delta", "D"),
                    CoordDecl::symbolic("mu", "D"),
                    CoordDecl::symbolic("rho", "D"),
                    CoordDecl::symbolic("B", "D"),
                    CoordDecl::symbolic("C", "D"),
                ],
                state_laws: vec![StateLaw {
                    name: "f_zero".into(),
                    kind: LawKind::Representation,
                    polynomial: f,
                    provenance: None,
                }],
                provenance: None,
            },
            PhaseDecl {
                name: "Busy".into(),
                coords: vec![
                    CoordDecl::symbolic("delta", "D"),
                    CoordDecl::symbolic("mu", "D"),
                    CoordDecl::symbolic("rho", "D"),
                    CoordDecl::symbolic("B", "D"),
                    CoordDecl::symbolic("C", "D"),
                    CoordDecl::symbolic("h", "D"),
                ],
                state_laws: vec![
                    StateLaw {
                        name: "f_zero".into(),
                        kind: LawKind::Representation,
                        polynomial: m.clone() * d.clone() * (one.clone() - r.clone()),
                        provenance: None,
                    },
                    StateLaw {
                        name: "busy_law".into(),
                        kind: LawKind::Representation,
                        polynomial: g_rho,
                        provenance: None,
                    },
                ],
                provenance: None,
            },
        ],
        operations: vec![
            OperationDecl {
                name: "begin".into(),
                source_phase: "Idle".into(),
                target_phase: "Busy".into(),
                args: vec![],
                domain_laws: vec![],
                updates: BTreeMap::from([
                    ("delta".into(), d.clone()),
                    ("mu".into(), m.clone()),
                    ("rho".into(), r.clone()),
                    ("B".into(), PolyExpr::state("B")),
                    ("C".into(), PolyExpr::state("C")),
                    ("h".into(), PolyExpr::state("C")),
                ]),
                provenance: None,
            },
            OperationDecl {
                name: "apply".into(),
                source_phase: "Busy".into(),
                target_phase: "Busy".into(),
                args: vec![("u".into(), "D".into())],
                domain_laws: vec![],
                updates: BTreeMap::from([
                    ("delta".into(), d.clone()),
                    ("mu".into(), m.clone()),
                    ("rho".into(), r.clone()),
                    (
                        "B".into(),
                        PolyExpr::state("B") + (one.clone() - d.clone()) * PolyExpr::arg("u"),
                    ),
                    (
                        "C".into(),
                        PolyExpr::state("C") + d.clone() * PolyExpr::arg("u"),
                    ),
                    ("h".into(), PolyExpr::state("h")),
                ]),
                provenance: None,
            },
            OperationDecl {
                name: "finish".into(),
                source_phase: "Busy".into(),
                target_phase: "Idle".into(),
                args: vec![],
                domain_laws: vec![],
                updates: BTreeMap::from([
                    ("delta".into(), d.clone()),
                    ("mu".into(), m.clone()),
                    ("rho".into(), r.clone()),
                    (
                        "B".into(),
                        PolyExpr::state("B") + m.clone() * PolyExpr::state("h"),
                    ),
                    ("C".into(), finish_c),
                ]),
                provenance: None,
            },
            OperationDecl {
                name: "toggle_delta".into(),
                source_phase: "Idle".into(),
                target_phase: "Idle".into(),
                args: vec![],
                domain_laws: vec![
                    StateLaw {
                        name: "d0".into(),
                        kind: LawKind::Representation,
                        polynomial: d.clone(),
                        provenance: None,
                    },
                    StateLaw {
                        name: "post_f".into(),
                        kind: LawKind::Representation,
                        polynomial: m.clone() * (one.clone() - r.clone()),
                        provenance: None,
                    },
                ],
                updates: BTreeMap::from([
                    ("delta".into(), one.clone()),
                    ("mu".into(), m.clone()),
                    ("rho".into(), r.clone()),
                    ("B".into(), PolyExpr::state("B")),
                    ("C".into(), PolyExpr::state("C")),
                ]),
                provenance: None,
            },
            OperationDecl {
                name: "toggle_mu".into(),
                source_phase: "Idle".into(),
                target_phase: "Idle".into(),
                args: vec![],
                domain_laws: vec![
                    StateLaw {
                        name: "m0".into(),
                        kind: LawKind::Representation,
                        polynomial: m.clone(),
                        provenance: None,
                    },
                    StateLaw {
                        name: "post_f".into(),
                        kind: LawKind::Representation,
                        polynomial: d.clone() * (one.clone() - r.clone()),
                        provenance: None,
                    },
                ],
                updates: BTreeMap::from([
                    ("delta".into(), d.clone()),
                    ("mu".into(), one.clone()),
                    ("rho".into(), r.clone()),
                    ("B".into(), PolyExpr::state("B")),
                    ("C".into(), PolyExpr::state("C")),
                ]),
                provenance: None,
            },
            OperationDecl {
                name: "toggle_rho".into(),
                source_phase: "Idle".into(),
                target_phase: "Idle".into(),
                args: vec![],
                domain_laws: vec![StateLaw {
                    name: "r0".into(),
                    kind: LawKind::Representation,
                    polynomial: r.clone(),
                    provenance: None,
                }],
                updates: BTreeMap::from([
                    ("delta".into(), d),
                    ("mu".into(), m),
                    ("rho".into(), one.clone()),
                    ("B".into(), PolyExpr::state("B")),
                    ("C".into(), PolyExpr::state("C")),
                ]),
                provenance: None,
            },
        ],
        observations: vec![
            ObservationDecl {
                name: "read".into(),
                phase: "Idle".into(),
                components: vec![PolyExpr::state("B") + PolyExpr::state("C")],
                provenance: None,
            },
            ObservationDecl {
                name: "read".into(),
                phase: "Busy".into(),
                components: vec![PolyExpr::state("B") + PolyExpr::state("C")],
                provenance: None,
            },
        ],
        provenance: Provenance::new(vec![orig("enl")], vec![MathClause::G140P5Dot2]),
    };

    let cmp = ComparisonPair {
        before: old,
        after,
        state_comparisons: vec![
            StateComparison {
                after_phase: "Idle".into(),
                before_phase: "Single".into(),
                map: BTreeMap::from([("x".into(), PolyExpr::state("B") + PolyExpr::state("C"))]),
                provenance: None,
            },
            StateComparison {
                after_phase: "Busy".into(),
                before_phase: "Single".into(),
                map: BTreeMap::from([("x".into(), PolyExpr::state("B") + PolyExpr::state("C"))]),
                provenance: None,
            },
        ],
        word_translation: WordTranslation {
            entries: vec![
                TranslatedWord {
                    after_operation: "begin".into(),
                    steps: vec![],
                    provenance: None,
                },
                TranslatedWord {
                    after_operation: "apply".into(),
                    steps: vec![TranslatedStep {
                        before_operation: "apply".into(),
                        arg_exprs: vec![PolyExpr::arg("u")],
                    }],
                    provenance: None,
                },
                TranslatedWord {
                    after_operation: "finish".into(),
                    steps: vec![],
                    provenance: None,
                },
                TranslatedWord {
                    after_operation: "toggle_delta".into(),
                    steps: vec![],
                    provenance: None,
                },
                TranslatedWord {
                    after_operation: "toggle_mu".into(),
                    steps: vec![],
                    provenance: None,
                },
                TranslatedWord {
                    after_operation: "toggle_rho".into(),
                    steps: vec![],
                    provenance: None,
                },
            ],
        },
    };

    let spec = PathSpec {
        name: "p52".into(),
        kind: PathKind::EnlargedProtocolExecutionPath,
        direction: MorphismDirection::TimeOrder,
        query_mode: PathQueryMode::Find,
        length: Some(3),
        vertices: BTreeMap::new(),
        rules: vec![],
        start: None,
        end: None,
        protocol: Some(ProtocolExecutionSpec {
            comparison: cmp,
            start_phase: "Idle".into(),
            start_laws: vec![
                StateLaw {
                    name: "s_d".into(),
                    kind: LawKind::Representation,
                    polynomial: PolyExpr::state("delta"),
                    provenance: None,
                },
                StateLaw {
                    name: "s_m".into(),
                    kind: LawKind::Representation,
                    polynomial: PolyExpr::state("mu"),
                    provenance: None,
                },
                StateLaw {
                    name: "s_r".into(),
                    kind: LawKind::Representation,
                    polynomial: PolyExpr::state("rho"),
                    provenance: None,
                },
            ],
            end_phase: "Idle".into(),
            end_laws: vec![
                StateLaw {
                    name: "e_d".into(),
                    kind: LawKind::Representation,
                    polynomial: PolyExpr::state("delta") - one.clone(),
                    provenance: None,
                },
                StateLaw {
                    name: "e_m".into(),
                    kind: LawKind::Representation,
                    polynomial: PolyExpr::state("mu") - one.clone(),
                    provenance: None,
                },
                StateLaw {
                    name: "e_r".into(),
                    kind: LawKind::Representation,
                    polynomial: PolyExpr::state("rho") - one,
                    provenance: None,
                },
            ],
            allowed_ops: vec![
                "toggle_delta".into(),
                "toggle_mu".into(),
                "toggle_rho".into(),
            ],
        }),
        change_spec: ChangeSpec {
            name: "H".into(),
            coeff_domain: q,
            parameters: vec![],
            fixed: vec![],
            editable: vec![],
            provenance: Provenance::new(vec![orig("h")], vec![MathClause::G140P5Dot2]),
        },
        eval_condition: None,
        provenance: Provenance::new(vec![orig("p52")], vec![MathClause::G140P5Dot2]),
    };

    let out = solve_path_task(&CheckedPathTask::validate(spec).unwrap());
    assert_eq!(out.verdict, Verdict::Established);
    let detail = out.path.unwrap();
    assert_eq!(
        detail.path_kind,
        PathOutcomeKind::EnlargedProtocolExecutionPath
    );
    assert_eq!(detail.protocol_preservation_verified, Some(true));
    assert_eq!(detail.valid_paths.len(), 4);
    assert!(
        detail.rejected_candidates.iter().any(|c| c.failed_step == 2
            && c.intermediate_state["rho"] == "0"
            && c.residuals == ["1"])
    );
}
