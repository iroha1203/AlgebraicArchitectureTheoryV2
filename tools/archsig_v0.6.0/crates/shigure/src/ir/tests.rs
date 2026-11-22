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
            domain_laws: vec![],
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
                domain_laws: vec![],
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
                domain_laws: vec![],
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
                domain_laws: vec![],
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
                domain_laws: vec![],
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
    pair.after.phases[0].coords[0].value = CoordValue::Missing;
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
fn observed_and_missing_coord_values_are_distinguished_by_sum_type() {
    let sym = CoordDecl::symbolic("B", "B");
    let obs = CoordDecl::observed("B", "B", ScalarLit::rat(0, 1).unwrap());
    let mis = CoordDecl::missing("B", "B");
    assert!(!sym.is_missing());
    assert!(!obs.is_missing());
    assert!(mis.is_missing());
    assert_ne!(obs.value, mis.value);
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
fn affine_degree_check_distinguishes_state_parameter_and_unobserved() {
    let affine_term = PolyExpr::add(
        PolyExpr::mul(PolyExpr::param("a"), PolyExpr::state("B")),
        PolyExpr::mul(
            PolyExpr::mul(PolyExpr::param("mu"), PolyExpr::param("delta")),
            PolyExpr::arg("u"),
        ),
    );
    assert_eq!(affine_term.is_affine_in_state_and_args(), Some(true));
    assert_eq!(affine_term.max_state_arg_degree(), Some(1));

    let quadratic_state = PolyExpr::mul(PolyExpr::state("B"), PolyExpr::state("C"));
    assert_eq!(quadratic_state.is_affine_in_state_and_args(), Some(false));
    assert_eq!(quadratic_state.max_state_arg_degree(), Some(2));

    let unknown_term = PolyExpr::mul(PolyExpr::unobserved("slot.x", None), PolyExpr::state("B"));
    assert_eq!(unknown_term.max_state_arg_degree(), None);
    assert_eq!(unknown_term.is_affine_in_state_and_args(), None);
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
        diagram: None,
        path: None,
        transfer: None,
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

#[test]
fn same_name_before_and_after_presentations_are_rejected() {
    let (mut pair, spec, _) = ledger_snapshot_task();
    pair.after.name = pair.before.name.clone();
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::DuplicateDecl {
            kind: "presentation",
            ..
        })
    ));
}

#[test]
fn observation_missing_and_arity_mismatch_across_pair_are_rejected() {
    let (mut pair, spec, _) = ledger_snapshot_task();
    pair.after.observations.retain(|o| o.phase != "Busy");
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::MissingObservation {
            ref after_phase,
            ref observation,
            ..
        }) if after_phase == "Busy" && observation == "read"
    ));

    let (mut pair, spec, _) = ledger_snapshot_task();
    pair.after.observations[0]
        .components
        .push(PolyExpr::state("C"));
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::ArityMismatch {
            expected: 1,
            actual: 2,
            ..
        })
    ));
}

#[test]
fn standalone_eval_condition_checks_prime_modulus_and_non_empty_allowed_params() {
    let cond = EvalCondition {
        name: "UniversalCheck".into(),
        evaluations: vec![],
        equations: vec![],
        invertibles: vec![],
        point_domain: PointDomain::UniversalRing,
        provenance: Provenance::default(),
    };
    assert!(matches!(
        validate_eval_condition(
            cond.clone(),
            &CoeffDomain::Fp(BigUint::from(9u32)),
            &BTreeSet::new()
        ),
        Err(ValidationError::InvalidPrimeModulus { .. })
    ));

    let empty_param = BTreeSet::from([" ".to_owned()]);
    assert!(matches!(
        validate_eval_condition(cond, &CoeffDomain::Q, &empty_param),
        Err(ValidationError::EmptyName { .. })
    ));
}

#[test]
fn duplicate_fixed_or_editable_targets_and_invalid_source_refs_are_rejected() {
    let (pair, mut spec, _) = ledger_snapshot_task();
    let dup = spec.fixed[0].clone();
    spec.fixed.push(dup);
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::DuplicateDecl {
            kind: "fixed target",
            ..
        })
    ));

    let (pair, mut spec, _) = ledger_snapshot_task();
    let dup_edit = spec.editable[0].clone();
    spec.editable.push(dup_edit);
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::DuplicateDecl {
            kind: "editable target",
            ..
        })
    ));

    let (mut pair, spec, _) = ledger_snapshot_task();
    pair.before.provenance.origins[0].span = Some((10, 2));
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::InvalidSourceSpan {
            start: 10,
            end: 2,
            ..
        })
    ));

    let (mut pair, spec, _) = ledger_snapshot_task();
    pair.before.provenance.origins[0].origin_id = "  ".into();
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::EmptyName { .. })
    ));
}

#[test]
fn interaction_summary_distinguishes_zero_constant_and_multi_variable_ideals() {
    let zero_ideal = InteractionSummary {
        min_interacting_variables: None,
        max_vanishing_subset_size: Some(2),
        minimal_failing_subsets: vec![],
        parameters: vec!["delta".into(), "mu".into()],
    };
    let constant_ideal = InteractionSummary {
        min_interacting_variables: Some(0),
        max_vanishing_subset_size: None,
        minimal_failing_subsets: vec![vec![]],
        parameters: vec!["delta".into(), "mu".into()],
    };
    let mu_delta = InteractionSummary {
        min_interacting_variables: Some(2),
        max_vanishing_subset_size: Some(1),
        minimal_failing_subsets: vec![vec!["delta".into(), "mu".into()]],
        parameters: vec!["delta".into(), "mu".into()],
    };
    assert_ne!(
        zero_ideal.to_json().canonical(),
        constant_ideal.to_json().canonical()
    );
    assert!(
        mu_delta
            .to_json()
            .canonical()
            .contains(r#""min_interacting_variables":2"#)
    );
    assert!(
        mu_delta
            .to_json()
            .canonical()
            .contains(r#""max_vanishing_subset_size":1"#)
    );
    assert!(
        !zero_ideal
            .to_json()
            .canonical()
            .contains("min_interacting_variables")
    );
    assert!(
        !constant_ideal
            .to_json()
            .canonical()
            .contains("max_vanishing_subset_size")
    );
}

#[test]
fn state_dependent_word_translation_and_out_of_range_fp_literal_are_checked() {
    let (mut pair, spec, _) = ledger_snapshot_task();
    // G-140 P2.1: state-dependent argument expression in word translation (`apply(C)`).
    pair.word_translation.entries[1].steps[0].arg_exprs = vec![PolyExpr::state("C")];
    CheckedShigureTask::validate(pair, spec, None)
        .expect("state coordinate in source phase is valid in translated step arg_exprs");

    let p5 = BigUint::from(5u32);
    let bad_fp_pres = Presentation {
        name: "FpBadLit".into(),
        coeff_domain: CoeffDomain::Fp(p5.clone()),
        sorts: vec![SortDecl {
            name: "D".into(),
            rank: 1,
            coeff_domain: CoeffDomain::Fp(p5.clone()),
            provenance: None,
        }],
        phases: vec![PhaseDecl {
            name: "S".into(),
            coords: vec![CoordDecl::observed(
                "x",
                "D",
                ScalarLit::Fp {
                    value: BigUint::from(5u32),
                    modulus: p5,
                },
            )],
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![],
        observations: vec![],
        provenance: Provenance::default(),
    };
    assert!(matches!(
        validate_presentation(bad_fp_pres, &BTreeSet::new()),
        Err(ValidationError::InvalidFpLiteral { .. })
    ));
}

#[test]
fn rational_coeff_domain_rejects_integer_points_while_z_accepts_it() {
    let (pair, spec, mut eval_cond) = ledger_snapshot_task();
    eval_cond.point_domain = PointDomain::IntegerPoints;
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, Some(eval_cond)),
        Err(ValidationError::PointDomainMismatch {
            coeff_domain: CoeffDomain::Q,
            point_domain: PointDomain::IntegerPoints,
        })
    ));

    let z_cond = EvalCondition {
        name: "IntegerCheck".into(),
        evaluations: vec![],
        equations: vec![],
        invertibles: vec![],
        point_domain: PointDomain::IntegerPoints,
        provenance: Provenance::default(),
    };
    validate_eval_condition(z_cond, &CoeffDomain::Z, &BTreeSet::new())
        .expect("Z coefficient domain accepts IntegerPoints");
}

#[test]
fn standalone_validate_change_spec_rejects_undeclared_pair_params() {
    let (pair, mut spec, _) = ledger_snapshot_task();
    let allowed = BTreeSet::from(["delta".to_owned(), "mu".to_owned(), "rho".to_owned()]);
    let checked_pair = validate_comparison_pair(pair, &allowed).expect("pair validates");
    spec.parameters.retain(|p| p.name != "rho");
    assert!(matches!(
        validate_change_spec(spec, &checked_pair),
        Err(ValidationError::UnknownRef {
            kind: "parameter",
            ref name,
            ..
        }) if name == "rho"
    ));
}

#[test]
fn empty_optional_source_ref_fields_are_rejected() {
    let cases = [
        SourceRef::new("orig", OriginKind::StaticAnalysis).with_location("", "a.rs", None),
        SourceRef::new("orig", OriginKind::StaticAnalysis).with_location("src", "   ", None),
        SourceRef::new("orig", OriginKind::StaticAnalysis).with_atom_ref(""),
        SourceRef::new("orig", OriginKind::StaticAnalysis).with_law_declaration(" "),
    ];
    for bad_ref in cases {
        let (mut pair, spec, _) = ledger_snapshot_task();
        pair.before.provenance.origins[0] = bad_ref;
        assert!(matches!(
            CheckedShigureTask::validate(pair, spec, None),
            Err(ValidationError::EmptyName { .. })
        ));
    }
}

#[test]
fn domain_mismatch_zero_rank_empty_observation_and_missing_maps_are_rejected() {
    // DomainMismatch: before/after mismatch
    let (mut pair, spec, _) = ledger_snapshot_task();
    pair.after.coeff_domain = CoeffDomain::Z;
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::DomainMismatch { .. })
    ));

    // DomainMismatch: sort vs presentation
    let (mut pair, spec, _) = ledger_snapshot_task();
    pair.before.sorts[0].coeff_domain = CoeffDomain::Z;
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::DomainMismatch { .. })
    ));

    // DomainMismatch: ChangeSpec vs pair
    let (pair, mut spec, _) = ledger_snapshot_task();
    spec.coeff_domain = CoeffDomain::Z;
    for p in &mut spec.parameters {
        p.coeff_domain = CoeffDomain::Z;
    }
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::DomainMismatch { .. })
    ));

    // DomainMismatch: ScalarLit Z inside Q presentation
    let (mut pair, spec, _) = ledger_snapshot_task();
    pair.before.phases[0].state_laws[0].polynomial = PolyExpr::int(0);
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::DomainMismatch { .. })
    ));

    // ZeroRankSort
    let (mut pair, spec, _) = ledger_snapshot_task();
    pair.before.sorts[0].rank = 0;
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::ZeroRankSort { .. })
    ));

    // EmptyObservation
    let (mut pair, spec, _) = ledger_snapshot_task();
    pair.before.observations[0].components.clear();
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::EmptyObservation { .. })
    ));

    // MissingStateComparison
    let (mut pair, spec, _) = ledger_snapshot_task();
    pair.state_comparisons.pop();
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::MissingStateComparison { .. })
    ));

    // MissingWordTranslation
    let (mut pair, spec, _) = ledger_snapshot_task();
    pair.word_translation.entries.pop();
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::MissingWordTranslation { .. })
    ));
}

#[test]
fn multistep_word_translation_phase_chain_and_fixed_law_kind_mismatches_are_rejected() {
    // Non-empty multi-step word translation with broken intermediate phase chain
    let (mut pair, spec, _) = ledger_snapshot_task();
    pair.before.phases.push(PhaseDecl {
        name: "Alt".into(),
        coords: vec![CoordDecl::symbolic("x", "D")],
        state_laws: vec![],
        provenance: None,
    });
    pair.before.operations.push(OperationDecl {
        name: "to_alt".into(),
        source_phase: "Single".into(),
        target_phase: "Alt".into(),
        args: vec![],
        domain_laws: vec![],
        updates: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
        provenance: None,
    });
    pair.word_translation.entries[1].steps = vec![
        TranslatedStep {
            before_operation: "to_alt".into(),
            arg_exprs: vec![],
        },
        TranslatedStep {
            before_operation: "apply".into(),
            arg_exprs: vec![PolyExpr::arg("u")],
        },
    ];
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::PhasePathMismatch { .. })
    ));

    // FixedTarget::SemanticLaw pointing to a Representation law is rejected
    let (pair, mut spec, _) = ledger_snapshot_task();
    spec.fixed.push(FixedTarget::SemanticLaw {
        presentation: "SnapshotLedger".into(),
        phase: "Busy".into(),
        law: "busy_snapshot_law".into(),
    });
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::UnknownRef {
            kind: "semantic",
            ..
        })
    ));

    // FixedTarget::RepresentationLaw pointing to a Semantic law is rejected
    let (pair, mut spec, _) = ledger_snapshot_task();
    spec.fixed[0] = FixedTarget::RepresentationLaw {
        presentation: "SingleLedger".into(),
        phase: "Single".into(),
        law: "semantic_identity".into(),
    };
    assert!(matches!(
        CheckedShigureTask::validate(pair, spec, None),
        Err(ValidationError::UnknownRef {
            kind: "representation",
            ..
        })
    ));
}
