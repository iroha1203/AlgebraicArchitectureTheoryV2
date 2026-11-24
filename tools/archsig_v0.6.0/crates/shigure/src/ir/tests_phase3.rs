use crate::ir::change::{ChangeSpec, EditableTarget, NamedPoly, PointDomain};
use crate::ir::family::{
    CandidateFamilySpec, CandidateMember, CandidateSpace, CheckedFamilySpec, FamilySpec,
    GoodnessKind, GoodnessSpec, PreservationGoodnessSource, RawSequenceCheck,
    ReadingComparisonSpec, RealizationFamilySpec, RealizationMember, RealizationSpace,
};
use crate::ir::observation::{
    CandidateObservationDecl, CheckedObservationTask, LawReadoutSpec, ObservationTaskSpec,
};
use crate::ir::presentation::{
    ComparisonPair, CoordDecl, CoordValue, LawKind, ObservationDecl, OperationDecl, PhaseDecl,
    Presentation, SortDecl, StateComparison, StateLaw, TranslatedStep, TranslatedWord,
    WordTranslation,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{ApplicabilityCheck, ReevalCheck, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_phase3::{
    ChevalleyOutcomeDetail, ChevalleyRegionSummary, CommonQuantifierResult,
    FiberNonEmptinessResult, ObservationOutcomeDetail, RobustnessOutcomeDetail,
};
use crate::ir::robustness::{
    CandidateSelector, CheckedChevalleyTask, CheckedRobustnessTask, ChevalleyTaskSpec,
    RationalFiberProbe, RobustnessTaskSpec,
};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::ir::validate::ValidationError;
use archsig_common::canonical::Json;
use num_bigint::BigInt;
use std::collections::BTreeMap;

fn origin(id: &str, kind: OriginKind) -> SourceRef {
    SourceRef::new(id, kind)
}

fn q(n: i64) -> ScalarLit {
    ScalarLit::rat(n, 1).expect("integer rational")
}

fn w4_family() -> FamilySpec {
    let mut u0 = BTreeMap::new();
    u0.insert("u".to_owned(), CoordValue::Observed(q(0)));
    let mut u1 = BTreeMap::new();
    u1.insert("u".to_owned(), CoordValue::Observed(q(1)));

    let mut c0 = BTreeMap::new();
    c0.insert("c".to_owned(), CoordValue::Observed(q(0)));
    let mut c1 = BTreeMap::new();
    c1.insert("c".to_owned(), CoordValue::Observed(q(1)));

    FamilySpec {
        name: "W4".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["u".to_owned()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::FiniteMembers(vec![
                RealizationMember {
                    id: "u0".to_owned(),
                    assignments: u0,
                    is_raw_candidate: false,
                    presentation: None,
                    origin: origin("obs-u0", OriginKind::StaticAnalysis),
                },
                RealizationMember {
                    id: "u1".to_owned(),
                    assignments: u1,
                    is_raw_candidate: true,
                    presentation: None,
                    origin: origin("obs-u1", OriginKind::LlmCandidate),
                },
            ]),
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec!["c".to_owned()],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![
                CandidateMember {
                    id: "c0".to_owned(),
                    assignments: c0,
                    origin: origin("cand-c0", OriginKind::HumanAdopted),
                },
                CandidateMember {
                    id: "c1".to_owned(),
                    assignments: c1,
                    origin: origin("cand-c1", OriginKind::RuntimeObservation),
                },
            ]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new(
                "diag",
                PolyExpr::diff(PolyExpr::param("u"), PolyExpr::param("c")),
            )],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: Provenance::new(
            vec![origin("fam", OriginKind::HumanAdopted)],
            vec![MathClause::G140E3, MathClause::G142G1],
        ),
    }
}

#[test]
fn checked_family_and_robustness_chevalley_observation_tasks_validate_invariants() {
    let fam = w4_family();
    let checked_fam = CheckedFamilySpec::validate(fam.clone()).expect("valid W4 family");
    assert_eq!(checked_fam.u_vars(), &["u"]);
    assert_eq!(checked_fam.c_vars(), &["c"]);
    assert!(checked_fam.unobserved_slots().is_empty());

    let rob = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "W4_rob".to_owned(),
        family: fam.clone(),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        designated_candidate: Some(CandidateSelector::ById("c0".to_owned())),
        check_universal_ring: false,
        fine_base_value: None,
        provenance: Provenance::new(vec![], vec![MathClause::G140E4, MathClause::G142G2]),
    })
    .expect("valid robustness task");
    assert_eq!(rob.name(), "W4_rob");

    let chev = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "W4_chev".to_owned(),
        family: fam.clone(),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: None,
        designated_candidate: Some(CandidateSelector::ById("c1".to_owned())),
        rational_fiber_probes: vec![RationalFiberProbe {
            name: "probe0".to_owned(),
            u_assignments: BTreeMap::from([("u".to_owned(), q(0))]),
            c_assignments: BTreeMap::new(),
        }],
        check_global_regular_section: false,
        check_universal_ring: true,
        provenance: Provenance::new(vec![], vec![MathClause::G141D7, MathClause::G142G7]),
    })
    .expect("valid chevalley task");
    assert_eq!(chev.name(), "W4_chev");

    let obs = CheckedObservationTask::validate(ObservationTaskSpec {
        name: "W4_obs".to_owned(),
        family: fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        observations: vec![CandidateObservationDecl {
            id: "e1".to_owned(),
            components: vec![NamedPoly::new("v", PolyExpr::param("u"))],
            cost: Some(BigInt::from(3)),
            origin: origin("obs-e1", OriginKind::StaticAnalysis),
        }],
        law_readout: Some(LawReadoutSpec {
            name: "const_read".to_owned(),
            components: vec![NamedPoly::new("r", PolyExpr::rat(0, 1).unwrap())],
            provenance: Provenance::default(),
        }),
        provenance: Provenance::new(vec![], vec![MathClause::G142G5, MathClause::G142G6]),
    })
    .expect("valid observation task");
    assert_eq!(obs.observations().len(), 1);
}

#[test]
fn checked_phase3_ir_rejects_domain_overlap_missing_origin_and_partial_costs() {
    // Variable overlap between u_vars and c_vars
    let mut bad_overlap = w4_family();
    bad_overlap.candidates.c_vars = vec!["u".to_owned()];
    assert!(matches!(
        CheckedFamilySpec::validate(bad_overlap),
        Err(ValidationError::ConversionError { .. })
    ));

    // Existential without witness_vars
    let mut bad_exist = w4_family();
    bad_exist.goodness = GoodnessSpec::Existential {
        witness_vars: vec![],
        equations: vec![],
        invertibles: vec![],
        preservation: None,
    };
    assert!(matches!(
        CheckedFamilySpec::validate(bad_exist),
        Err(ValidationError::ConversionError { .. })
    ));

    // Missing origin_id in realization member
    let mut bad_origin = w4_family();
    if let RealizationSpace::FiniteMembers(ref mut ms) = bad_origin.realizations.space {
        ms[0].origin.origin_id.clear();
    }
    assert!(matches!(
        CheckedFamilySpec::validate(bad_origin),
        Err(ValidationError::EmptyName { .. })
    ));

    // Chevalley rejects non-AlgebraicClosure point_domain
    assert!(matches!(
        CheckedChevalleyTask::validate(ChevalleyTaskSpec {
            name: "bad_chev".to_owned(),
            family: w4_family(),
            point_domain: PointDomain::RationalPoints,
            base_value: None,
            designated_candidate: None,
            rational_fiber_probes: vec![],
            check_global_regular_section: false,
            check_universal_ring: false,
            provenance: Provenance::default(),
        }),
        Err(ValidationError::PointDomainMismatch { .. })
    ));

    // Observation task rejects partial costs (some Some, some None)
    assert!(matches!(
        CheckedObservationTask::validate(ObservationTaskSpec {
            name: "bad_obs".to_owned(),
            family: w4_family(),
            point_domain: PointDomain::AlgebraicClosure,
            base_value: vec![],
            observations: vec![
                CandidateObservationDecl {
                    id: "e1".to_owned(),
                    components: vec![NamedPoly::new("v", PolyExpr::param("u"))],
                    cost: Some(BigInt::from(1)),
                    origin: origin("o1", OriginKind::StaticAnalysis),
                },
                CandidateObservationDecl {
                    id: "e2".to_owned(),
                    components: vec![NamedPoly::new("v", PolyExpr::rat(1, 1).unwrap())],
                    cost: None,
                    origin: origin("o2", OriginKind::RuntimeObservation),
                },
            ],
            law_readout: None,
            provenance: Provenance::default(),
        }),
        Err(ValidationError::ConversionError { .. })
    ));

    // Fine base value without reading_comparison is rejected
    assert!(matches!(
        CheckedRobustnessTask::validate(RobustnessTaskSpec {
            name: "bad_fine".to_owned(),
            family: w4_family(),
            point_domain: PointDomain::AlgebraicClosure,
            base_value: vec![],
            designated_candidate: None,
            check_universal_ring: false,
            fine_base_value: Some(vec![q(0)]),
            provenance: Provenance::default(),
        }),
        Err(ValidationError::ConversionError { .. })
    ));

    // Non-prime modulus Fp(4) is rejected
    let mut bad_prime = w4_family();
    bad_prime.coeff_domain = CoeffDomain::Fp(4u32.into());
    assert!(matches!(
        CheckedFamilySpec::validate(bad_prime),
        Err(ValidationError::InvalidPrimeModulus { .. })
    ));

    // CoordValue::Symbolic in FiniteMembers is rejected
    let mut bad_symbolic_real = w4_family();
    if let RealizationSpace::FiniteMembers(ref mut ms) = bad_symbolic_real.realizations.space {
        ms[0]
            .assignments
            .insert("u".to_owned(), CoordValue::Symbolic);
    }
    assert!(matches!(
        CheckedFamilySpec::validate(bad_symbolic_real),
        Err(ValidationError::ConversionError { .. })
    ));

    let mut bad_symbolic_cand = w4_family();
    if let CandidateSpace::FiniteMembers(ref mut ms) = bad_symbolic_cand.candidates.space {
        ms[0]
            .assignments
            .insert("c".to_owned(), CoordValue::Symbolic);
    }
    assert!(matches!(
        CheckedFamilySpec::validate(bad_symbolic_cand),
        Err(ValidationError::ConversionError { .. })
    ));

    // Empty raw_sequence.steps is rejected
    let mut bad_empty_steps = w4_family();
    bad_empty_steps.goodness = GoodnessSpec::Direct {
        equations: vec![],
        invertibles: vec![],
        preservation: None,
        raw_sequence: Some(RawSequenceCheck {
            start_phase: "Idle".to_owned(),
            start_state: BTreeMap::from([("B".to_owned(), q(0))]),
            steps: vec![],
            observation_name: "read".to_owned(),
            baseline_step_index: None,
            provenance: Provenance::default(),
        }),
    };
    assert!(matches!(
        CheckedFamilySpec::validate(bad_empty_steps),
        Err(ValidationError::ConversionError { .. })
    ));

    // Negative observation cost is rejected
    assert!(matches!(
        CheckedObservationTask::validate(ObservationTaskSpec {
            name: "bad_neg_cost".to_owned(),
            family: w4_family(),
            point_domain: PointDomain::AlgebraicClosure,
            base_value: vec![],
            observations: vec![CandidateObservationDecl {
                id: "e1".to_owned(),
                components: vec![NamedPoly::new("v", PolyExpr::param("u"))],
                cost: Some(BigInt::from(-1)),
                origin: origin("o1", OriginKind::StaticAnalysis),
            }],
            law_readout: None,
            provenance: Provenance::default(),
        }),
        Err(ValidationError::ConversionError { .. })
    ));

    // PreservationGoodnessSource rejects marking LawKind::Semantic editable
    let make_pres = |pres_name: &str| Presentation {
        name: pres_name.to_owned(),
        coeff_domain: CoeffDomain::Q,
        sorts: vec![SortDecl {
            name: "S".to_owned(),
            rank: 1,
            coeff_domain: CoeffDomain::Q,
            provenance: None,
        }],
        phases: vec![PhaseDecl {
            name: "Active".to_owned(),
            coords: vec![CoordDecl::symbolic("x", "S")],
            state_laws: vec![StateLaw {
                name: "sem_ok".to_owned(),
                kind: LawKind::Semantic,
                polynomial: PolyExpr::state("x"),
                provenance: None,
            }],
            provenance: None,
        }],
        operations: vec![],
        observations: vec![],
        provenance: Provenance::default(),
    };
    let mut bad_sem_fam = w4_family();
    bad_sem_fam.goodness = GoodnessSpec::Direct {
        equations: vec![],
        invertibles: vec![],
        preservation: Some(PreservationGoodnessSource {
            pair: ComparisonPair {
                before: make_pres("Before"),
                after: make_pres("After"),
                state_comparisons: vec![StateComparison {
                    after_phase: "Active".to_owned(),
                    before_phase: "Active".to_owned(),
                    map: BTreeMap::from([("x".to_owned(), PolyExpr::state("x"))]),
                    provenance: None,
                }],
                word_translation: WordTranslation::default(),
            },
            change_spec: ChangeSpec {
                name: "H".to_owned(),
                coeff_domain: CoeffDomain::Q,
                parameters: vec![],
                fixed: vec![],
                editable: vec![EditableTarget::RepresentationLaw {
                    presentation: "After".to_owned(),
                    phase: "Active".to_owned(),
                    law: "sem_ok".to_owned(),
                }],
                provenance: Provenance::default(),
            },
            param_bindings: BTreeMap::new(),
        }),
        raw_sequence: None,
    };
    assert!(matches!(
        CheckedFamilySpec::validate(bad_sem_fam),
        Err(ValidationError::SemanticLawEditable { .. })
    ));
}

fn raw_ledger_pres(name: &str) -> Presentation {
    Presentation {
        name: name.to_owned(),
        coeff_domain: CoeffDomain::Q,
        sorts: vec![SortDecl {
            name: "S".to_owned(),
            rank: 1,
            coeff_domain: CoeffDomain::Q,
            provenance: None,
        }],
        phases: vec![
            PhaseDecl {
                name: "Idle".to_owned(),
                coords: vec![CoordDecl::symbolic("B", "S")],
                state_laws: vec![],
                provenance: None,
            },
            PhaseDecl {
                name: "Busy".to_owned(),
                coords: vec![CoordDecl::symbolic("B", "S")],
                state_laws: vec![],
                provenance: None,
            },
        ],
        operations: vec![
            OperationDecl {
                name: "begin".to_owned(),
                source_phase: "Idle".to_owned(),
                target_phase: "Busy".to_owned(),
                args: vec![],
                domain_laws: vec![],
                updates: BTreeMap::from([("B".to_owned(), PolyExpr::state("B"))]),
                provenance: None,
            },
            OperationDecl {
                name: "apply_1".to_owned(),
                source_phase: "Busy".to_owned(),
                target_phase: "Busy".to_owned(),
                args: vec![("x".to_owned(), "S".to_owned())],
                domain_laws: vec![],
                updates: BTreeMap::from([(
                    "B".to_owned(),
                    PolyExpr::sum(PolyExpr::state("B"), PolyExpr::arg("x")),
                )]),
                provenance: None,
            },
            OperationDecl {
                name: "finish".to_owned(),
                source_phase: "Busy".to_owned(),
                target_phase: "Idle".to_owned(),
                args: vec![],
                domain_laws: vec![],
                updates: BTreeMap::from([("B".to_owned(), PolyExpr::state("B"))]),
                provenance: None,
            },
        ],
        observations: vec![
            ObservationDecl {
                name: "read".to_owned(),
                phase: "Idle".to_owned(),
                components: vec![PolyExpr::state("B")],
                provenance: None,
            },
            ObservationDecl {
                name: "read".to_owned(),
                phase: "Busy".to_owned(),
                components: vec![PolyExpr::state("B")],
                provenance: None,
            },
        ],
        provenance: Provenance::default(),
    }
}

#[test]
fn unobserved_slots_in_family_and_raw_sequence_reading_comparison_validate() {
    let mut fam = w4_family();
    if let RealizationSpace::FiniteMembers(ref mut ms) = fam.realizations.space {
        ms[0]
            .assignments
            .insert("u".to_owned(), CoordValue::Missing);
    }
    fam.reading_comparison = Some(ReadingComparisonSpec {
        name: "fine_vs_coarse".to_owned(),
        fine_b_vars: vec!["bf".to_owned()],
        fine_q: vec![PolyExpr::unobserved("fine_u", None)],
        coarsen_r: vec![],
        provenance: Provenance::default(),
    });
    fam.goodness = GoodnessSpec::Direct {
        equations: vec![NamedPoly::new(
            "g_unobs",
            PolyExpr::unobserved("goodness_u", None),
        )],
        invertibles: vec![],
        preservation: Some(PreservationGoodnessSource {
            pair: ComparisonPair {
                before: raw_ledger_pres("Before"),
                after: raw_ledger_pres("After"),
                state_comparisons: vec![
                    StateComparison {
                        after_phase: "Idle".to_owned(),
                        before_phase: "Idle".to_owned(),
                        map: BTreeMap::from([(
                            "B".to_owned(),
                            PolyExpr::unobserved("h_unobs", None),
                        )]),
                        provenance: None,
                    },
                    StateComparison {
                        after_phase: "Busy".to_owned(),
                        before_phase: "Busy".to_owned(),
                        map: BTreeMap::from([("B".to_owned(), PolyExpr::state("B"))]),
                        provenance: None,
                    },
                ],
                word_translation: WordTranslation {
                    entries: vec![
                        TranslatedWord {
                            after_operation: "begin".to_owned(),
                            steps: vec![TranslatedStep {
                                before_operation: "begin".to_owned(),
                                arg_exprs: vec![],
                            }],
                            provenance: None,
                        },
                        TranslatedWord {
                            after_operation: "apply_1".to_owned(),
                            steps: vec![TranslatedStep {
                                before_operation: "apply_1".to_owned(),
                                arg_exprs: vec![PolyExpr::unobserved("tau_unobs", None)],
                            }],
                            provenance: None,
                        },
                        TranslatedWord {
                            after_operation: "finish".to_owned(),
                            steps: vec![TranslatedStep {
                                before_operation: "finish".to_owned(),
                                arg_exprs: vec![],
                            }],
                            provenance: None,
                        },
                    ],
                },
            },
            change_spec: ChangeSpec {
                name: "H".to_owned(),
                coeff_domain: CoeffDomain::Q,
                parameters: vec![],
                fixed: vec![],
                editable: vec![],
                provenance: Provenance::default(),
            },
            param_bindings: BTreeMap::new(),
        }),
        raw_sequence: None,
    };
    let checked = CheckedFamilySpec::validate(fam.clone()).expect("valid unobserved collection");
    let slots = checked.unobserved_slots();
    assert!(slots.contains(&"W4.realization.u0.u".to_owned()));
    assert!(slots.contains(&"fine_u".to_owned()));
    assert!(slots.contains(&"goodness_u".to_owned()));
    assert!(slots.contains(&"h_unobs".to_owned()));
    assert!(slots.contains(&"tau_unobs".to_owned()));

    let obs_task = CheckedObservationTask::validate(ObservationTaskSpec {
        name: "obs_unobs".to_owned(),
        family: fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        observations: vec![CandidateObservationDecl {
            id: "e1".to_owned(),
            components: vec![NamedPoly::new(
                "v",
                PolyExpr::unobserved("obs_e1_unobs", None),
            )],
            cost: None,
            origin: origin("o1", OriginKind::StaticAnalysis),
        }],
        law_readout: Some(LawReadoutSpec {
            name: "lr".to_owned(),
            components: vec![NamedPoly::new(
                "v",
                PolyExpr::unobserved("readout_unobs", None),
            )],
            provenance: Provenance::default(),
        }),
        provenance: Provenance::default(),
    })
    .unwrap();
    let obs_slots = obs_task.unobserved_slots();
    assert!(obs_slots.contains(&"obs_e1_unobs".to_owned()));
    assert!(obs_slots.contains(&"readout_unobs".to_owned()));

    // Raw sequence validation: valid presentation passes; missing/invalid references rejected
    let valid_seq = RawSequenceCheck {
        start_phase: "Idle".to_owned(),
        start_state: BTreeMap::from([("B".to_owned(), q(0))]),
        steps: vec![
            ("begin".to_owned(), vec![]),
            ("apply_1".to_owned(), vec![q(1)]),
            ("finish".to_owned(), vec![]),
        ],
        observation_name: "read".to_owned(),
        baseline_step_index: Some(1),
        provenance: Provenance::default(),
    };
    let mut raw_fam = w4_family();
    raw_fam.goodness = GoodnessSpec::Direct {
        equations: vec![],
        invertibles: vec![],
        preservation: None,
        raw_sequence: Some(valid_seq.clone()),
    };
    // Member presentation: None is rejected
    assert!(matches!(
        CheckedFamilySpec::validate(raw_fam.clone()),
        Err(ValidationError::ConversionError { .. })
    ));

    // Attach real presentations -> passes
    if let RealizationSpace::FiniteMembers(ref mut ms) = raw_fam.realizations.space {
        for (i, m) in ms.iter_mut().enumerate() {
            m.presentation = Some(raw_ledger_pres(&format!("M{i}")));
        }
    }
    assert!(CheckedFamilySpec::validate(raw_fam.clone()).is_ok());

    // PolynomialScheme with raw_sequence is rejected
    let mut raw_scheme = raw_fam.clone();
    raw_scheme.realizations.space = RealizationSpace::PolynomialScheme {
        equations: vec![],
        invertibles: vec![],
        is_raw_candidate: true,
        origin: origin("scheme", OriginKind::StaticAnalysis),
    };
    assert!(matches!(
        CheckedFamilySpec::validate(raw_scheme),
        Err(ValidationError::ConversionError { .. })
    ));

    // Unknown start_phase / coord / operation / phase chain / arity / observation rejected
    let set_seq = |base: &FamilySpec, seq: RawSequenceCheck| {
        let mut f = base.clone();
        f.goodness = GoodnessSpec::Direct {
            equations: vec![],
            invertibles: vec![],
            preservation: None,
            raw_sequence: Some(seq),
        };
        CheckedFamilySpec::validate(f)
    };
    assert!(matches!(
        set_seq(
            &raw_fam,
            RawSequenceCheck {
                start_phase: "NoSuchPhase".to_owned(),
                ..valid_seq.clone()
            }
        ),
        Err(ValidationError::UnknownRef { kind: "phase", .. })
    ));
    assert!(matches!(
        set_seq(
            &raw_fam,
            RawSequenceCheck {
                start_state: BTreeMap::from([("UnknownCoord".to_owned(), q(0))]),
                ..valid_seq.clone()
            }
        ),
        Err(ValidationError::UnknownRef {
            kind: "state coordinate",
            ..
        })
    ));
    assert!(matches!(
        set_seq(
            &raw_fam,
            RawSequenceCheck {
                steps: vec![("no_op".to_owned(), vec![])],
                baseline_step_index: None,
                ..valid_seq.clone()
            }
        ),
        Err(ValidationError::UnknownRef {
            kind: "operation",
            ..
        })
    ));
    assert!(matches!(
        set_seq(
            &raw_fam,
            RawSequenceCheck {
                steps: vec![("finish".to_owned(), vec![])],
                baseline_step_index: None,
                ..valid_seq.clone()
            }
        ),
        Err(ValidationError::PhasePathMismatch { .. })
    ));
    assert!(matches!(
        set_seq(
            &raw_fam,
            RawSequenceCheck {
                steps: vec![("begin".to_owned(), vec![]), ("apply_1".to_owned(), vec![])],
                baseline_step_index: None,
                ..valid_seq.clone()
            }
        ),
        Err(ValidationError::ArityMismatch { .. })
    ));
    assert!(matches!(
        set_seq(
            &raw_fam,
            RawSequenceCheck {
                observation_name: "no_obs".to_owned(),
                ..valid_seq.clone()
            }
        ),
        Err(ValidationError::UnknownRef {
            kind: "observation",
            ..
        })
    ));

    // Omitted baseline_step_index (None) checks observation at pre-final state:
    // 1) multi-step checks phase after penultimate step (`Busy`)
    assert!(
        set_seq(
            &raw_fam,
            RawSequenceCheck {
                baseline_step_index: None,
                ..valid_seq.clone()
            }
        )
        .is_ok()
    );
    let mut no_busy_obs = raw_fam.clone();
    if let RealizationSpace::FiniteMembers(ref mut ms) = no_busy_obs.realizations.space {
        for m in ms.iter_mut() {
            m.presentation
                .as_mut()
                .unwrap()
                .observations
                .retain(|o| o.phase != "Busy");
        }
    }
    assert!(matches!(
        set_seq(
            &no_busy_obs,
            RawSequenceCheck {
                baseline_step_index: None,
                ..valid_seq.clone()
            }
        ),
        Err(ValidationError::UnknownRef {
            kind: "observation",
            ..
        })
    ));

    // 2) 1-step sequence with baseline_step_index = None checks start_phase (`Idle`)
    let single_step_seq = RawSequenceCheck {
        steps: vec![("begin".to_owned(), vec![])],
        baseline_step_index: None,
        ..valid_seq
    };
    assert!(set_seq(&raw_fam, single_step_seq.clone()).is_ok());
    let mut no_idle_obs = raw_fam;
    if let RealizationSpace::FiniteMembers(ref mut ms) = no_idle_obs.realizations.space {
        for m in ms.iter_mut() {
            m.presentation
                .as_mut()
                .unwrap()
                .observations
                .retain(|o| o.phase != "Idle");
        }
    }
    assert!(matches!(
        set_seq(&no_idle_obs, single_step_seq),
        Err(ValidationError::UnknownRef {
            kind: "observation",
            ..
        })
    ));
}

#[test]
fn phase3_math_clauses_and_outcome_json_render_cleanly() {
    assert_eq!(MathClause::G140E3.stable_id(), "shigure:G-140:E3");
    assert_eq!(MathClause::G140E5Dot1.stable_id(), "shigure:G-140:E5.1");
    assert_eq!(MathClause::G140P7.stable_id(), "shigure:G-140:P7");
    assert_eq!(MathClause::G141D6.stable_id(), "shigure:G-141:D6");
    assert_eq!(MathClause::G141D7.stable_id(), "shigure:G-141:D7");
    assert_eq!(MathClause::G142G5.stable_id(), "shigure:G-142:G5");
    assert_eq!(MathClause::G142G7.stable_id(), "shigure:G-142:G7");

    let empty_region = ChevalleyRegionSummary {
        strata: vec![],
        is_empty: true,
    };
    let outcome = ShigureOutcome {
        verdict: Verdict::Undetermined(SilenceReason::ConstructibleStratificationOutOfScope {
            detail: "branch limit exceeded".to_owned(),
        }),
        coeff_domain: CoeffDomain::Q,
        point_domain: PointDomain::AlgebraicClosure,
        applicability: vec![ApplicabilityCheck::failed(
            "d6_stratification",
            MathClause::G141D6,
            "branch limit",
        )],
        provenance: Provenance::new(
            vec![origin("o1", OriginKind::StaticAnalysis)],
            vec![MathClause::G141D6],
        ),
        residual_ideal: vec![],
        empty_witness: None,
        restored: None,
        interaction: None,
        diagram: None,
        path: None,
        transfer: None,
        robustness: Some(RobustnessOutcomeDetail {
            goodness_kind: GoodnessKind::Existential,
            fiber_non_empty: FiberNonEmptinessResult {
                non_empty: false,
                status: "empty_realizations".to_owned(),
                witness: None,
                empty_witness: None,
            },
            valid_designated: None,
            pointwise: None,
            common_candidate: Some(CommonQuantifierResult {
                satisfied: false,
                vacuously_true_empty_fiber: false,
                candidate_id: None,
                candidate_assignments: None,
                witnesses: vec![],
                counterexample_witnesses: vec![],
                counterexample_detail: Some("no common candidate".to_owned()),
            }),
            universal_ring: None,
            reading_comparison: None,
        }),
        chevalley: Some(ChevalleyOutcomeDetail {
            goodness_kind: GoodnessKind::Direct,
            point_domain: PointDomain::AlgebraicClosure,
            effective_image_e: None,
            p_plus: empty_region.clone(),
            p_minus: empty_region.clone(),
            robust_all_pass: empty_region.clone(),
            all_fail: empty_region.clone(),
            mixed: empty_region.clone(),
            empty_realizations: empty_region,
            designated_candidate_class: None,
            mixed_witness_pair: None,
            rational_fiber_probes: vec![],
            global_regular_section: None,
            universal_ring_contrast: None,
        }),
        observations: Some(ObservationOutcomeDetail {
            sufficient: true,
            distinguishing_pair_count: 0,
            distinguishing_pairs: vec![],
            insufficiency_witness: None,
            minimal_sufficient_sets: vec![],
            cost_ranked_sets: vec![],
            law_readout_comparison: None,
        }),
        lift: None,
        artin: None,
        diagnostics: None,
        atlas: None,
    };
    let json = outcome.to_json();
    let Json::Obj(map) = &json else {
        panic!("expected Json::Obj");
    };
    assert!(map.contains_key("robustness"));
    assert!(map.contains_key("chevalley"));
    assert!(map.contains_key("observations"));
    if let Some(Json::Obj(rob)) = map.get("robustness")
        && let Some(Json::Obj(common)) = rob.get("common_candidate")
    {
        assert!(!common.contains_key("candidate_assignments"));
        assert!(common.contains_key("counterexample_witnesses"));
    } else {
        panic!("expected robustness.common_candidate object");
    }
    assert_eq!(
        ReevalCheck {
            checked: true,
            matched: true,
            detail: "ok".to_owned(),
        }
        .to_json(),
        Json::obj([
            ("checked", Json::Bool(true)),
            ("matched", Json::Bool(true)),
            ("detail", Json::str("ok")),
            ("scope", Json::str("mathematical_model_reevaluation")),
        ])
    );
}
