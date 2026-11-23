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
    ComparisonPair, CoordDecl, CoordValue, LawKind, PhaseDecl, Presentation, SortDecl,
    StateComparison, StateLaw, WordTranslation,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{ApplicabilityCheck, ReevalCheck, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_phase3::{
    ChevalleyOutcomeDetail, ChevalleyRegionSummary, FiberNonEmptinessResult,
    ObservationOutcomeDetail, RobustnessOutcomeDetail,
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
        fine_q: vec![PolyExpr::param("u")],
        coarsen_r: vec![],
        provenance: Provenance::default(),
    });
    let checked = CheckedFamilySpec::validate(fam).expect("valid missing assignment");
    assert_eq!(
        checked.unobserved_slots(),
        vec!["W4.realization.u0.u".to_owned()]
    );

    let mut raw_fam = w4_family();
    raw_fam.goodness = GoodnessSpec::Direct {
        equations: vec![],
        invertibles: vec![],
        preservation: None,
        raw_sequence: Some(RawSequenceCheck {
            start_phase: "Idle".to_owned(),
            start_state: BTreeMap::from([("B".to_owned(), q(0))]),
            steps: vec![("begin".to_owned(), vec![]), ("finish".to_owned(), vec![])],
            observation_name: "read".to_owned(),
            baseline_step_index: Some(0),
            provenance: Provenance::default(),
        }),
    };
    assert!(CheckedFamilySpec::validate(raw_fam).is_ok());
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
            common_candidate: None,
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
    };
    let json = outcome.to_json();
    let Json::Obj(map) = &json else {
        panic!("expected Json::Obj");
    };
    assert!(map.contains_key("robustness"));
    assert!(map.contains_key("chevalley"));
    assert!(map.contains_key("observations"));
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
