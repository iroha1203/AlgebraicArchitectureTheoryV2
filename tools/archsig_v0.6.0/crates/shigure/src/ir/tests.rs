use super::*;
use num_bigint::{BigInt, BigUint};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::{Add, Mul, Sub};

fn q(n: i64) -> PolyExpr {
    PolyExpr::rat(n, 1).expect("denominator 1 is valid")
}

fn ledger_snapshot_task() -> (ComparisonPair, ChangeSpec, EvalCondition) {
    let origin = SourceRef::new("orig-spec", OriginKind::HumanAdopted).with_location(
        "src-ledger",
        "ledger.rs",
        Some((0, 42)),
    );

    let before = Presentation {
        name: "SingleLedger".into(),
        coeff_domain: CoeffDomain::Q,
        sorts: vec![SortDecl {
            name: "D".into(),
            rank: 1,
            coeff_domain: CoeffDomain::Q,
            provenance: Some(origin.clone()),
        }],
        phases: vec![PhaseDecl {
            name: "Single".into(),
            coords: vec![CoordDecl::symbolic("x", "D")],
            state_laws: vec![StateLaw {
                name: "semantic_identity".into(),
                kind: LawKind::Semantic,
                polynomial: q(0),
                provenance: Some(origin.clone()),
            }],
            provenance: Some(origin.clone()),
        }],
        operations: vec![OperationDecl {
            name: "apply".into(),
            source_phase: "Single".into(),
            target_phase: "Single".into(),
            args: vec![("u".into(), "D".into())],
            updates: BTreeMap::from([(
                "x".into(),
                PolyExpr::add(PolyExpr::state("x"), PolyExpr::arg("u")),
            )]),
            provenance: Some(origin.clone()),
        }],
        observations: vec![ObservationDecl {
            name: "read".into(),
            phase: "Single".into(),
            components: vec![PolyExpr::state("x")],
            provenance: Some(origin.clone()),
        }],
        provenance: Provenance::new(
            vec![origin.clone()],
            vec![MathClause::G139P0P1, MathClause::G140P0Dot1],
        ),
    };

    let g_rho = PolyExpr::mul(
        PolyExpr::mul(
            PolyExpr::param("mu"),
            PolyExpr::sub(q(1), PolyExpr::param("rho")),
        ),
        PolyExpr::sub(PolyExpr::state("h"), PolyExpr::state("C")),
    );
    let after = Presentation {
        name: "SnapshotLedger".into(),
        coeff_domain: CoeffDomain::Q,
        sorts: vec![
            SortDecl {
                name: "D".into(),
                rank: 1,
                coeff_domain: CoeffDomain::Q,
                provenance: None,
            },
            SortDecl {
                name: "B".into(),
                rank: 1,
                coeff_domain: CoeffDomain::Q,
                provenance: None,
            },
            SortDecl {
                name: "C".into(),
                rank: 1,
                coeff_domain: CoeffDomain::Q,
                provenance: None,
            },
        ],
        phases: vec![
            PhaseDecl {
                name: "Idle".into(),
                coords: vec![CoordDecl::symbolic("B", "B"), CoordDecl::symbolic("C", "C")],
                state_laws: vec![],
                provenance: None,
            },
            PhaseDecl {
                name: "Busy".into(),
                coords: vec![
                    CoordDecl::symbolic("B", "B"),
                    CoordDecl::symbolic("C", "C"),
                    CoordDecl::symbolic("h", "C"),
                ],
                state_laws: vec![StateLaw {
                    name: "busy_snapshot_law".into(),
                    kind: LawKind::Representation,
                    polynomial: g_rho,
                    provenance: Some(SourceRef::new("orig-llm", OriginKind::LlmCandidate)),
                }],
                provenance: None,
            },
        ],
        operations: vec![
            OperationDecl {
                name: "begin".into(),
                source_phase: "Idle".into(),
                target_phase: "Busy".into(),
                args: vec![],
                updates: BTreeMap::from([
                    ("B".into(), PolyExpr::state("B")),
                    ("C".into(), PolyExpr::state("C")),
                    ("h".into(), PolyExpr::state("C")),
                ]),
                provenance: None,
            },
            OperationDecl {
                name: "apply_idle".into(),
                source_phase: "Idle".into(),
                target_phase: "Idle".into(),
                args: vec![("u".into(), "D".into())],
                updates: BTreeMap::from([
                    (
                        "B".into(),
                        PolyExpr::add(
                            PolyExpr::state("B"),
                            PolyExpr::mul(
                                PolyExpr::sub(q(1), PolyExpr::param("delta")),
                                PolyExpr::arg("u"),
                            ),
                        ),
                    ),
                    (
                        "C".into(),
                        PolyExpr::add(
                            PolyExpr::state("C"),
                            PolyExpr::mul(PolyExpr::param("delta"), PolyExpr::arg("u")),
                        ),
                    ),
                ]),
                provenance: None,
            },
            OperationDecl {
                name: "apply_busy".into(),
                source_phase: "Busy".into(),
                target_phase: "Busy".into(),
                args: vec![("u".into(), "D".into())],
                updates: BTreeMap::from([
                    (
                        "B".into(),
                        PolyExpr::add(
                            PolyExpr::state("B"),
                            PolyExpr::mul(
                                PolyExpr::sub(q(1), PolyExpr::param("delta")),
                                PolyExpr::arg("u"),
                            ),
                        ),
                    ),
                    (
                        "C".into(),
                        PolyExpr::add(
                            PolyExpr::state("C"),
                            PolyExpr::mul(PolyExpr::param("delta"), PolyExpr::arg("u")),
                        ),
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
                updates: BTreeMap::from([
                    (
                        "B".into(),
                        PolyExpr::add(
                            PolyExpr::state("B"),
                            PolyExpr::mul(PolyExpr::param("mu"), PolyExpr::state("h")),
                        ),
                    ),
                    (
                        "C".into(),
                        PolyExpr::sub(
                            PolyExpr::state("C"),
                            PolyExpr::mul(
                                PolyExpr::param("mu"),
                                PolyExpr::add(
                                    PolyExpr::mul(
                                        PolyExpr::sub(q(1), PolyExpr::param("rho")),
                                        PolyExpr::state("C"),
                                    ),
                                    PolyExpr::mul(PolyExpr::param("rho"), PolyExpr::state("h")),
                                ),
                            ),
                        ),
                    ),
                ]),
                provenance: None,
            },
        ],
        observations: vec![
            ObservationDecl {
                name: "read".into(),
                phase: "Idle".into(),
                components: vec![PolyExpr::add(PolyExpr::state("B"), PolyExpr::state("C"))],
                provenance: None,
            },
            ObservationDecl {
                name: "read".into(),
                phase: "Busy".into(),
                components: vec![PolyExpr::add(PolyExpr::state("B"), PolyExpr::state("C"))],
                provenance: None,
            },
        ],
        provenance: Provenance::new(
            vec![
                SourceRef::new("orig-static", OriginKind::StaticAnalysis),
                SourceRef::new("orig-runtime", OriginKind::RuntimeObservation),
            ],
            vec![MathClause::G140P3P5],
        ),
    };

    let pair = ComparisonPair {
        before,
        after,
        state_comparisons: vec![
            StateComparison {
                after_phase: "Idle".into(),
                before_phase: "Single".into(),
                map: BTreeMap::from([(
                    "x".into(),
                    PolyExpr::add(PolyExpr::state("B"), PolyExpr::state("C")),
                )]),
                provenance: None,
            },
            StateComparison {
                after_phase: "Busy".into(),
                before_phase: "Single".into(),
                map: BTreeMap::from([(
                    "x".into(),
                    PolyExpr::add(PolyExpr::state("B"), PolyExpr::state("C")),
                )]),
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
                    after_operation: "apply_idle".into(),
                    steps: vec![TranslatedStep {
                        before_operation: "apply".into(),
                        arg_exprs: vec![PolyExpr::arg("u")],
                    }],
                    provenance: None,
                },
                TranslatedWord {
                    after_operation: "apply_busy".into(),
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
            ],
        },
    };

    let change_spec = ChangeSpec {
        name: "AllowFinishRhoAndBusyLaw".into(),
        coeff_domain: CoeffDomain::Q,
        parameters: vec![
            ParamDecl {
                name: "delta".into(),
                coeff_domain: CoeffDomain::Q,
                provenance: None,
            },
            ParamDecl {
                name: "mu".into(),
                coeff_domain: CoeffDomain::Q,
                provenance: None,
            },
            ParamDecl {
                name: "rho".into(),
                coeff_domain: CoeffDomain::Q,
                provenance: None,
            },
        ],
        fixed: vec![
            FixedTarget::SemanticLaw {
                presentation: "SingleLedger".into(),
                phase: "Single".into(),
                law: "semantic_identity".into(),
            },
            FixedTarget::StateComparisonExpr {
                after_phase: "Idle".into(),
            },
            FixedTarget::WordTranslationOp {
                operation: "finish".into(),
            },
        ],
        editable: vec![
            EditableTarget::OperationExpr {
                presentation: "SnapshotLedger".into(),
                operation: "finish".into(),
            },
            EditableTarget::RepresentationLaw {
                presentation: "SnapshotLedger".into(),
                phase: "Busy".into(),
                law: "busy_snapshot_law".into(),
            },
        ],
        provenance: Provenance::new(vec![origin], vec![MathClause::G140E1E2, MathClause::G140P6]),
    };

    let eval_cond = EvalCondition {
        name: "ActiveDeltaAndCompaction".into(),
        evaluations: vec![
            NamedPoly::new("delta", PolyExpr::param("delta")),
            NamedPoly::new("mu", PolyExpr::param("mu")),
        ],
        equations: vec![],
        invertibles: vec![NamedPoly::new(
            "mu_delta",
            PolyExpr::mul(PolyExpr::param("mu"), PolyExpr::param("delta")),
        )],
        point_domain: PointDomain::AlgebraicClosure,
        provenance: Provenance::new(vec![], vec![MathClause::G140E1E2, MathClause::G141D5]),
    };

    (pair, change_spec, eval_cond)
}

#[test]
fn valid_ledger_snapshot_task_passes_validation_and_has_no_unobserved_slots() {
    let (pair, spec, eval_cond) = ledger_snapshot_task();
    let task = CheckedShigureTask::validate(pair, spec, Some(eval_cond))
        .expect("well-typed ledger snapshot IR must validate");
    assert!(task.unobserved_slots().is_empty());
    assert!(!task.eval_condition().unwrap().is_purely_closed());
}

#[test]
fn semantic_law_cannot_be_marked_editable() {
    let (pair, mut spec, eval_cond) = ledger_snapshot_task();
    spec.fixed.clear();
    spec.editable.push(EditableTarget::RepresentationLaw {
        presentation: "SingleLedger".into(),
        phase: "Single".into(),
        law: "semantic_identity".into(),
    });
    let err = CheckedShigureTask::validate(pair, spec, Some(eval_cond)).unwrap_err();
    assert!(matches!(err, ValidationError::SemanticLawEditable { .. }));
}

#[test]
fn fixed_and_editable_conflict_is_rejected() {
    let (pair, mut spec, eval_cond) = ledger_snapshot_task();
    spec.fixed.push(FixedTarget::RepresentationLaw {
        presentation: "SnapshotLedger".into(),
        phase: "Busy".into(),
        law: "busy_snapshot_law".into(),
    });
    let err = CheckedShigureTask::validate(pair, spec, Some(eval_cond)).unwrap_err();
    assert!(matches!(err, ValidationError::FixedEditableConflict { .. }));
}

#[test]
fn non_prime_fp_modulus_is_rejected() {
    let pres = Presentation {
        name: "BadFp".into(),
        coeff_domain: CoeffDomain::Fp(BigUint::from(9u32)),
        sorts: vec![],
        phases: vec![],
        operations: vec![],
        observations: vec![],
        provenance: Provenance::default(),
    };
    let err = validate_presentation(pres, &BTreeSet::new()).unwrap_err();
    assert!(matches!(err, ValidationError::InvalidPrimeModulus { .. }));
}

#[test]
fn unobserved_coordinates_and_terms_are_preserved_not_zeroed() {
    let (mut pair, spec, eval_cond) = ledger_snapshot_task();
    pair.after.phases[0].coords[0].missing = true;
    pair.after.operations[0].updates.insert(
        "h".into(),
        PolyExpr::unobserved("SnapshotLedger.Idle.h_init", None),
    );
    let task = CheckedShigureTask::validate(pair, spec, Some(eval_cond))
        .expect("missing slots are valid IR inputs");
    let slots = task.unobserved_slots();
    assert_eq!(
        slots,
        vec![
            "SnapshotLedger.Idle.B".to_owned(),
            "SnapshotLedger.Idle.h_init".to_owned()
        ]
    );
}

#[test]
fn conflicting_missing_and_observed_coordinate_is_rejected() {
    let (mut pair, spec, eval_cond) = ledger_snapshot_task();
    pair.after.phases[0].coords[0].missing = true;
    pair.after.phases[0].coords[0].observed_value = ScalarLit::rat(1, 1);
    let err = CheckedShigureTask::validate(pair, spec, Some(eval_cond)).unwrap_err();
    assert!(matches!(
        err,
        ValidationError::ConflictingObservationState { .. }
    ));
}

#[test]
fn point_domain_mismatch_and_unknown_references_are_rejected() {
    let (pair, spec, mut eval_cond) = ledger_snapshot_task();
    eval_cond.point_domain = PointDomain::FiniteFieldPoints(BigUint::from(5u32));
    let err = CheckedShigureTask::validate(pair, spec, Some(eval_cond)).unwrap_err();
    assert!(matches!(err, ValidationError::PointDomainMismatch { .. }));

    let (pair2, spec2, mut eval_cond2) = ledger_snapshot_task();
    eval_cond2
        .equations
        .push(NamedPoly::new("bad", PolyExpr::param("undeclared_var")));
    let err2 = CheckedShigureTask::validate(pair2, spec2, Some(eval_cond2)).unwrap_err();
    assert!(matches!(
        err2,
        ValidationError::UnknownRef {
            kind: "parameter",
            ..
        }
    ));
}

#[test]
fn unreduced_or_zero_denominator_rational_is_rejected() {
    assert!(ScalarLit::rat(1, 0).is_none());
    let reduced = ScalarLit::rat(-4, -6).unwrap();
    assert_eq!(
        reduced,
        ScalarLit::Q {
            num: BigInt::from(2),
            den: BigInt::from(3),
        }
    );

    let (mut pair, spec, eval_cond) = ledger_snapshot_task();
    pair.before.phases[0].state_laws[0].polynomial = PolyExpr::Const(ScalarLit::Q {
        num: BigInt::from(2),
        den: BigInt::from(4),
    });
    let err = CheckedShigureTask::validate(pair, spec, Some(eval_cond)).unwrap_err();
    assert!(matches!(err, ValidationError::InvalidRational { .. }));
}

#[test]
fn affine_degree_check_distinguishes_state_and_parameter_products() {
    let affine_term = PolyExpr::add(
        PolyExpr::mul(PolyExpr::param("a"), PolyExpr::state("B")),
        PolyExpr::mul(
            PolyExpr::mul(PolyExpr::param("mu"), PolyExpr::param("delta")),
            PolyExpr::arg("u"),
        ),
    );
    assert!(affine_term.is_affine_in_state_and_args());

    let quadratic_state = PolyExpr::mul(PolyExpr::state("B"), PolyExpr::state("C"));
    assert!(!quadratic_state.is_affine_in_state_and_args());
    assert_eq!(quadratic_state.max_state_arg_degree(), 2);
}

#[test]
fn outcome_json_preserves_domains_silence_and_origin_kinds() {
    for kind in [
        OriginKind::StaticAnalysis,
        OriginKind::RuntimeObservation,
        OriginKind::LlmCandidate,
        OriginKind::HumanAdopted,
    ] {
        assert_eq!(OriginKind::from_wire(kind.wire()), Some(kind));
    }

    let outcome = ShigureOutcome {
        verdict: Verdict::Undetermined(SilenceReason::NonLinearRationalOrIntegerExistence {
            point_domain: PointDomain::RationalPoints,
            detail: "x^2 + 1 = 0 is nonempty over algebraic closure, but rational point existence is outside affine scope".into(),
        }),
        coeff_domain: CoeffDomain::Q,
        point_domain: PointDomain::RationalPoints,
        applicability: vec![ApplicabilityCheck::failed(
            "rational_point_existence",
            MathClause::G141D5,
            "nonlinear ideal over Q",
        )],
        provenance: Provenance::new(
            vec![SourceRef::new("obs-1", OriginKind::StaticAnalysis)],
            vec![MathClause::G141D5],
        ),
        residual_ideal: vec!["x^2 + 1".into()],
        empty_witness: None,
        restored: None,
        interaction: None,
    };
    let rendered = outcome.to_json().canonical();
    assert!(rendered.contains(r#""verdict":"undetermined""#));
    assert!(rendered.contains(r#""point_domain":"Q_points""#));
    assert!(rendered.contains(r#""code":"nonlinear_point_existence_out_of_scope""#));
    assert!(rendered.contains(r#""shigure:G-141:D5""#));
    assert!(rendered.contains(r#""result_kind":"mathematical_computation""#));
}

#[test]
fn duplicate_missing_update_arity_and_phase_path_errors_are_detected() {
    let (mut pair, spec, _) = ledger_snapshot_task();
    pair.before.sorts.push(pair.before.sorts[0].clone());
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::DuplicateDecl { kind: "sort", .. })
    ));

    let (mut pair, spec, _) = ledger_snapshot_task();
    pair.after.operations[0].updates.remove("h");
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::MissingCoordUpdate { .. })
    ));

    let (mut pair, spec, _) = ledger_snapshot_task();
    pair.after.operations[0]
        .updates
        .insert("ghost".into(), q(0));
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::UnknownCoordUpdate { .. })
    ));

    let (mut pair, spec, _) = ledger_snapshot_task();
    pair.word_translation.entries[1].steps[0].arg_exprs.clear();
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::ArityMismatch { .. })
    ));

    let (mut pair, spec, _) = ledger_snapshot_task();
    pair.before.phases.push(PhaseDecl {
        name: "AltSingle".into(),
        coords: vec![CoordDecl::symbolic("x", "D")],
        state_laws: vec![],
        provenance: None,
    });
    pair.state_comparisons[1].before_phase = "AltSingle".into();
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::PhasePathMismatch { .. })
    ));
}
