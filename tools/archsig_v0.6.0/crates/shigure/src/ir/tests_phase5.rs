//! Phase 5 検証済み IR（`occurrence`, `partial`, `revision`, `multisource`）および
//! `result_phase5_*` の単体テスト。

use super::multisource::{
    CandidateRecordSpec, MultisourceTaskSpec, SourcePresentationSpec, SupportGoalFormula,
    SupportGoalSpec, validate_multisource_task,
};
use super::occurrence::{
    OccurrenceOpSpec, OccurrenceSortSpec, OccurrenceTaskSpec, validate_occurrence_task,
};
use super::partial::{
    FinitePartialPresentation, PartialEvalLawSpec, PartialFormula, PartialOpSignature,
    PartialRecordKind, PartialRecordSpec, PartialRepresentation, PartialSlotDecl, PartialTaskSpec,
    PartialTerm, PartialTruth, validate_partial_task,
};
use super::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use super::result::{ShigureOutcome, SilenceReason, Verdict};
use super::revision::{
    RevisionConstraintSpec, RevisionCoordSpec, RevisionKind, RevisionPredicate, RevisionSideSpec,
    RevisionTaskSpec, validate_revision_task,
};
use super::term::{CoeffDomain, ScalarLit};
use super::validate::ValidationError;
use crate::ir::change::PointDomain;
use std::collections::{BTreeMap, BTreeSet};

fn sample_prov() -> Provenance {
    Provenance::new(
        vec![SourceRef::new("obs_src", OriginKind::StaticAnalysis)],
        vec![MathClause::AatCh17Thm17Dot2],
    )
}

#[test]
fn occurrence_ir_accepts_valid_and_rejects_unknown_sort() {
    let valid = OccurrenceTaskSpec {
        name: "occ_test".into(),
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
        identity_requests: vec![("S".into(), "a".into(), "b".into())],
        op_records: vec![],
        pred_records: vec![],
        base_readings: vec![],
        context_closed_17_5: true,
        explicit_contexts: vec![],
        preserve_full_domains: vec![],
        initial_readouts: vec![],
        provenance: sample_prov(),
        max_congruence_steps: 0,
        max_partitions: 0,
        undeclared_unobserved_slots: vec![],
    };
    let checked = validate_occurrence_task(valid.clone()).expect("valid occurrence IR");
    assert_eq!(checked.name(), "occ_test");

    let mut bad = valid;
    bad.identity_requests
        .push(("UnknownSort".into(), "a".into(), "b".into()));
    assert!(matches!(
        validate_occurrence_task(bad),
        Err(ValidationError::UnknownRef { kind: "sort", .. })
    ));
}

#[test]
fn partial_ir_separates_absent_from_slot_and_rejects_unknown_slot() {
    let valid = PartialTaskSpec {
        name: "part_test".into(),
        representation: PartialRepresentation::FiniteTable(FinitePartialPresentation {
            sorts: BTreeMap::from([("V".into(), vec!["0".into(), "1".into()])]),
            operations: vec![PartialOpSignature {
                name: "f".into(),
                arg_sorts: vec!["V".into()],
                out_sort: "V".into(),
                is_total: false,
            }],
            relations: vec![],
            slots: vec![PartialSlotDecl {
                name: "xi".into(),
                sort: "V".into(),
                domain_values: vec!["0".into(), "1".into()],
            }],
            background_constraints: vec![],
            records: vec![PartialRecordSpec {
                id: "r1".into(),
                kind: PartialRecordKind::OpDomain {
                    op_name: "f".into(),
                    args: vec!["0".into()],
                    defined: PartialTruth::ExplicitAbsent,
                },
            }],
            max_completions: 64,
        }),
        eval_laws: vec![PartialEvalLawSpec {
            name: "l1".into(),
            antecedent: None,
            conclusion: PartialFormula::Eq(
                PartialTerm::Slot("xi".into()),
                PartialTerm::Const("0".into()),
            ),
            is_required_law: true,
        }],
        quantifier_spec: None,
        open_domain: None,
        provenance: sample_prov(),
        undeclared_unobserved_slots: vec![],
    };
    assert!(validate_partial_task(valid.clone()).is_ok());

    let mut bad = valid;
    bad.eval_laws[0].conclusion = PartialFormula::Eq(
        PartialTerm::Slot("undeclared_slot".into()),
        PartialTerm::Const("0".into()),
    );
    assert!(matches!(
        validate_partial_task(bad),
        Err(ValidationError::UnknownRef { kind: "slot", .. })
    ));
}

#[test]
fn revision_and_multisource_ir_validate_constraints_and_mixed_costs() {
    let rev = RevisionTaskSpec {
        name: "rev_test".into(),
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
        ],
        shared_constraints: vec![RevisionConstraintSpec {
            id: "c_eq".into(),
            support: vec!["xi".into(), "eta".into()],
            predicate: RevisionPredicate::Equality("xi".into(), "eta".into()),
        }],
        before: RevisionSideSpec {
            assignments: BTreeMap::from([("xi".into(), ScalarLit::int(0))]),
            extra_constraints: vec![],
        },
        after: RevisionSideSpec {
            assignments: BTreeMap::from([("xi".into(), ScalarLit::int(1))]),
            extra_constraints: vec![],
        },
        explicit_delta_coords: vec!["xi".into()],
        probes: vec![],
        snf_spec: None,
        max_completions: 64,
        provenance: sample_prov(),
        undeclared_unobserved_slots: vec![],
    };
    assert!(validate_revision_task(rev).is_ok());

    let ms = MultisourceTaskSpec {
        name: "ms_test".into(),
        coeff_domain: CoeffDomain::Z,
        coords: vec![RevisionCoordSpec {
            id: "x".into(),
            domain_values: vec![ScalarLit::int(0), ScalarLit::int(1)],
        }],
        background_constraints: vec![],
        sources: vec![SourcePresentationSpec {
            source_id: "s1".into(),
            origin: SourceRef::new("s1", OriginKind::StaticAnalysis),
            assignments: BTreeMap::from([("x".into(), ScalarLit::int(0))]),
            forbidden_values: vec![],
            extra_constraints: vec![],
        }],
        support_goal: Some(SupportGoalSpec {
            trusted_assignments: BTreeMap::new(),
            candidates: vec![
                CandidateRecordSpec {
                    id: "h1".into(),
                    coord: "x".into(),
                    value: ScalarLit::int(0),
                    cost: Some(ScalarLit::int(1)),
                    origin: SourceRef::new("c1", OriginKind::LlmCandidate),
                    verified_actual_value: None,
                },
                CandidateRecordSpec {
                    id: "h2".into(),
                    coord: "x".into(),
                    value: ScalarLit::int(1),
                    cost: None,
                    origin: SourceRef::new("c2", OriginKind::LlmCandidate),
                    verified_actual_value: None,
                },
            ],
            goal: SupportGoalFormula::CoordEqualsConst("x".into(), ScalarLit::int(0)),
            expected_truth: true,
            check_post_adoption_stability: true,
        }),
        max_sources_subset_steps: 0,
        max_results: 0,
        provenance: sample_prov(),
        undeclared_unobserved_slots: vec![],
    };
    assert!(matches!(
        validate_multisource_task(ms),
        Err(ValidationError::ConversionError { .. })
    ));

    let silence_outcome = ShigureOutcome {
        verdict: Verdict::Undetermined(SilenceReason::UnsupportedCompletionClass {
            detail: "nonlinear".into(),
        }),
        coeff_domain: CoeffDomain::Q,
        point_domain: PointDomain::RationalPoints,
        applicability: vec![],
        provenance: sample_prov(),
        residual_ideal: vec![],
        empty_witness: None,
        restored: None,
        interaction: None,
        diagram: None,
        path: None,
        transfer: None,
        robustness: None,
        chevalley: None,
        observations: None,
        lift: None,
        artin: None,
        diagnostics: None,
        atlas: None,
        occurrence: None,
        partial: None,
        revision: None,
        multisource: None,
    };
    let json = silence_outcome.to_json().canonical();
    assert!(json.contains("unsupported_completion_class"));
}

#[test]
fn phase5_ir_rejects_missing_support_arity_mismatch_fp_cost_and_contradictory_snf() {
    use super::multisource::{MultisourceTaskSpec, SourcePresentationSpec};
    use super::occurrence::{
        OccurrenceOpSpec, OccurrenceReadingSpec, OccurrenceRelSpec, OccurrenceSortSpec,
    };
    use super::revision::SnfRevisionSpec;
    use crate::algebra::congruence::{PredicateRecord, PredicateRecordKind};
    use num_bigint::BigUint;

    // 1. revision: support に述語参照座標が含まれない場合拒否 ([中心-2])
    let bad_rev = RevisionTaskSpec {
        name: "bad_sup".into(),
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
        ],
        shared_constraints: vec![RevisionConstraintSpec {
            id: "c_eq".into(),
            support: vec!["xi".into()],
            predicate: RevisionPredicate::Equality("xi".into(), "eta".into()),
        }],
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
        snf_spec: None,
        max_completions: 0,
        provenance: sample_prov(),
        undeclared_unobserved_slots: vec![],
    };
    assert!(matches!(
        validate_revision_task(bad_rev),
        Err(ValidationError::ConversionError { .. })
    ));

    // 2. revision: origin_label_only なのに rhs が異なる矛盾拒否 ([非中心-3])
    let bad_snf = RevisionTaskSpec {
        name: "bad_snf".into(),
        kind: RevisionKind::Span,
        coeff_domain: CoeffDomain::Z,
        coords: vec![RevisionCoordSpec {
            id: "x".into(),
            domain_values: vec![ScalarLit::int(0)],
        }],
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
            coeff_domain: CoeffDomain::Z,
            m_before: vec![vec![ScalarLit::int(2)]],
            m_after: vec![vec![ScalarLit::int(2)]],
            num_cols: 1,
            rhs_before: vec![ScalarLit::int(2)],
            rhs_after: vec![ScalarLit::int(4)],
            op_in_common_p0: true,
            op_uniquely_determined: true,
            force_reuse_existing_snf: false,
            origin_label_only: true,
        }),
        max_completions: 0,
        provenance: sample_prov(),
        undeclared_unobserved_slots: vec![],
    };
    assert!(matches!(
        validate_revision_task(bad_snf),
        Err(ValidationError::ConversionError { .. })
    ));

    // 3. multisource: Fp 費用および support 漏れを拒否 ([非中心-1], [中心-2])
    let bad_ms = MultisourceTaskSpec {
        name: "bad_ms_fp".into(),
        coeff_domain: CoeffDomain::Z,
        coords: vec![RevisionCoordSpec {
            id: "x".into(),
            domain_values: vec![ScalarLit::int(0), ScalarLit::int(1)],
        }],
        background_constraints: vec![],
        sources: vec![SourcePresentationSpec {
            source_id: "s1".into(),
            origin: SourceRef::new("s1", OriginKind::StaticAnalysis),
            assignments: BTreeMap::new(),
            forbidden_values: vec![],
            extra_constraints: vec![],
        }],
        support_goal: Some(SupportGoalSpec {
            trusted_assignments: BTreeMap::new(),
            candidates: vec![CandidateRecordSpec {
                id: "h1".into(),
                coord: "x".into(),
                value: ScalarLit::int(0),
                cost: Some(ScalarLit::Fp {
                    value: BigUint::from(1u32),
                    modulus: BigUint::from(3u32),
                }),
                origin: SourceRef::new("c1", OriginKind::LlmCandidate),
                verified_actual_value: None,
            }],
            goal: SupportGoalFormula::CoordEqualsConst("x".into(), ScalarLit::int(0)),
            expected_truth: true,
            check_post_adoption_stability: true,
        }),
        max_sources_subset_steps: 0,
        max_results: 0,
        provenance: sample_prov(),
        undeclared_unobserved_slots: vec![],
    };
    assert!(matches!(
        validate_multisource_task(bad_ms),
        Err(ValidationError::ConversionError { .. })
    ));

    // 4. occurrence: pred_records アリティ不一致・setting 17.5 不完全読取りを拒否 ([中心-3])
    let bad_occ_arity = OccurrenceTaskSpec {
        name: "bad_occ".into(),
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
        relations: vec![OccurrenceRelSpec {
            name: "R".into(),
            arg_sorts: vec!["S".into(), "S".into()],
        }],
        identity_requests: vec![],
        op_records: vec![],
        pred_records: vec![PredicateRecord {
            name: "R".into(),
            kind: PredicateRecordKind::Relation,
            arg_sorts: vec!["S".into(), "S".into()],
            args: vec!["a".into()],
            positive: true,
        }],
        base_readings: vec![],
        context_closed_17_5: true,
        explicit_contexts: vec![],
        preserve_full_domains: vec![],
        initial_readouts: vec![],
        provenance: sample_prov(),
        max_congruence_steps: 0,
        max_partitions: 0,
        undeclared_unobserved_slots: vec![],
    };
    assert!(matches!(
        validate_occurrence_task(bad_occ_arity),
        Err(ValidationError::ArityMismatch { .. })
    ));

    let bad_occ_reading = OccurrenceTaskSpec {
        name: "bad_occ_read".into(),
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
            name: "o".into(),
            sort: "S".into(),
            values: BTreeMap::from([("a".into(), Some("0".into()))]),
        }],
        context_closed_17_5: true,
        explicit_contexts: vec![],
        preserve_full_domains: vec![],
        initial_readouts: vec![],
        provenance: sample_prov(),
        max_congruence_steps: 0,
        max_partitions: 0,
        undeclared_unobserved_slots: vec![],
    };
    assert!(matches!(
        validate_occurrence_task(bad_occ_reading),
        Err(ValidationError::ConversionError { .. })
    ));

    // 5. partial: 有限表のアリティ不一致・空評価 Law 名・アフィン行重複を拒否 ([中心-3])
    let bad_part = PartialTaskSpec {
        name: "bad_part".into(),
        representation: PartialRepresentation::FiniteTable(FinitePartialPresentation {
            sorts: BTreeMap::from([("V".into(), vec!["0".into(), "1".into()])]),
            operations: vec![PartialOpSignature {
                name: "f".into(),
                arg_sorts: vec!["V".into()],
                out_sort: "V".into(),
                is_total: false,
            }],
            relations: vec![],
            slots: vec![],
            background_constraints: vec![],
            records: vec![PartialRecordSpec {
                id: "r1".into(),
                kind: PartialRecordKind::OpValue {
                    op_name: "f".into(),
                    args: vec![],
                    value: super::partial::PartialValue::Known("0".into()),
                },
            }],
            max_completions: 16,
        }),
        eval_laws: vec![],
        quantifier_spec: None,
        open_domain: None,
        provenance: sample_prov(),
        undeclared_unobserved_slots: vec![],
    };
    assert!(matches!(
        validate_partial_task(bad_part),
        Err(ValidationError::ArityMismatch { .. })
    ));

    let _ = BTreeSet::<String>::new();
}

#[test]
fn phase5_ir_rejects_empty_origins_bad_open_domain_restricted_domain_and_unreduced_q_cost() {
    use super::multisource::{MultisourceTaskSpec, SourcePresentationSpec};
    use super::occurrence::{OccurrenceSortSpec, OccurrenceTaskSpec};
    use super::partial::{
        FiberCoverageCheckSpec, OpenDomainSpec, OpenOpTable, PartialEvalLawSpec, PartialFormula,
        PartialTaskSpec, PartialTerm,
    };
    use super::revision::{RevisionCoordSpec, RevisionKind, RevisionSideSpec, RevisionTaskSpec};

    let empty_prov = Provenance::new(vec![], vec![MathClause::AatCh17Thm17Dot2]);

    // 1. All 4 specs reject empty origins
    assert!(matches!(
        validate_occurrence_task(OccurrenceTaskSpec {
            name: "no_orig_occ".into(),
            sorts: vec![OccurrenceSortSpec {
                name: "S".into(),
                elements: vec!["a".into()],
                is_fixed_value: false,
            }],
            operations: vec![],
            relations: vec![],
            identity_requests: vec![],
            op_records: vec![],
            pred_records: vec![],
            base_readings: vec![],
            context_closed_17_5: true,
            explicit_contexts: vec![],
            preserve_full_domains: vec![],
            initial_readouts: vec![],
            provenance: empty_prov.clone(),
            max_congruence_steps: 0,
            max_partitions: 0,
            undeclared_unobserved_slots: vec![],
        }),
        Err(ValidationError::ConversionError { .. })
    ));
    assert!(matches!(
        validate_partial_task(PartialTaskSpec {
            name: "no_orig_part".into(),
            representation: PartialRepresentation::UnsupportedClass {
                description: "none".into(),
            },
            eval_laws: vec![],
            quantifier_spec: None,
            open_domain: None,
            provenance: empty_prov.clone(),
            undeclared_unobserved_slots: vec![],
        }),
        Err(ValidationError::ConversionError { .. })
    ));
    assert!(matches!(
        validate_revision_task(RevisionTaskSpec {
            name: "no_orig_rev".into(),
            kind: RevisionKind::Extension,
            coeff_domain: CoeffDomain::Z,
            coords: vec![RevisionCoordSpec {
                id: "x".into(),
                domain_values: vec![ScalarLit::int(0)],
            }],
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
            snf_spec: None,
            max_completions: 0,
            provenance: empty_prov.clone(),
            undeclared_unobserved_slots: vec![],
        }),
        Err(ValidationError::ConversionError { .. })
    ));
    assert!(matches!(
        validate_multisource_task(MultisourceTaskSpec {
            name: "no_orig_ms".into(),
            coeff_domain: CoeffDomain::Z,
            coords: vec![RevisionCoordSpec {
                id: "x".into(),
                domain_values: vec![ScalarLit::int(0)],
            }],
            background_constraints: vec![],
            sources: vec![SourcePresentationSpec {
                source_id: "s1".into(),
                origin: SourceRef::new("s1", OriginKind::StaticAnalysis),
                assignments: BTreeMap::new(),
                forbidden_values: vec![],
                extra_constraints: vec![],
            }],
            support_goal: None,
            max_sources_subset_steps: 0,
            max_results: 0,
            provenance: empty_prov,
            undeclared_unobserved_slots: vec![],
        }),
        Err(ValidationError::ConversionError { .. })
    ));

    // 2. partial: restricted_domain unknown element & open_domain bad fiber / out-of-carrier entry
    let bad_restricted = PartialTaskSpec {
        name: "bad_restricted".into(),
        representation: PartialRepresentation::FiniteTable(FinitePartialPresentation {
            sorts: BTreeMap::from([("V".into(), vec!["0".into(), "1".into()])]),
            operations: vec![],
            relations: vec![],
            slots: vec![],
            background_constraints: vec![],
            records: vec![],
            max_completions: 8,
        }),
        eval_laws: vec![PartialEvalLawSpec {
            name: "q".into(),
            antecedent: None,
            conclusion: PartialFormula::Exists {
                var: "x".into(),
                sort: "V".into(),
                restricted_domain: Some(vec!["999".into()]),
                body: Box::new(PartialFormula::Eq(
                    PartialTerm::Var("x".into()),
                    PartialTerm::Var("x".into()),
                )),
            },
            is_required_law: true,
        }],
        quantifier_spec: None,
        open_domain: None,
        provenance: sample_prov(),
        undeclared_unobserved_slots: vec![],
    };
    assert!(matches!(
        validate_partial_task(bad_restricted),
        Err(ValidationError::UnknownRef {
            kind: "occurrence",
            ..
        })
    ));

    let bad_open_sig = PartialTaskSpec {
        name: "bad_open_sig".into(),
        representation: PartialRepresentation::UnsupportedClass {
            description: "open_only".into(),
        },
        eval_laws: vec![],
        quantifier_spec: None,
        open_domain: Some(OpenDomainSpec {
            substructure_carriers: BTreeMap::from([
                ("A".into(), vec!["a0".into()]),
                ("B".into(), vec!["b0".into()]),
            ]),
            ambient_carriers: BTreeMap::from([
                ("A".into(), vec!["a0".into(), "a1".into()]),
                ("B".into(), vec!["b0".into(), "b1".into()]),
            ]),
            substructure_ops: vec![OpenOpTable {
                name: "rho".into(),
                arg_sorts: vec!["A".into(), "A".into()],
                out_sort: "B".into(),
                entries: BTreeMap::new(),
            }],
            ambient_ops: vec![OpenOpTable {
                name: "rho".into(),
                arg_sorts: vec!["A".into(), "A".into()],
                out_sort: "B".into(),
                entries: BTreeMap::new(),
            }],
            substructure_rels: vec![],
            ambient_rels: vec![],
            fiber_checks: vec![FiberCoverageCheckSpec {
                op_name: "rho".into(),
                arg_sort: "A".into(),
                target_sort: "B".into(),
                known_targets: vec!["b0".into()],
            }],
            positive_or_law: PartialEvalLawSpec {
                name: "pos".into(),
                antecedent: None,
                conclusion: PartialFormula::Eq(
                    PartialTerm::Const("a0".into()),
                    PartialTerm::Const("a0".into()),
                ),
                is_required_law: true,
            },
            affine_restriction: None,
        }),
        provenance: sample_prov(),
        undeclared_unobserved_slots: vec![],
    };
    assert!(matches!(
        validate_partial_task(bad_open_sig),
        Err(ValidationError::ConversionError { .. })
    ));

    // 3. multisource: unreduced rational cost (2/4 or -1/-2) rejected
    let unreduced_ms = MultisourceTaskSpec {
        name: "unreduced_q".into(),
        coeff_domain: CoeffDomain::Q,
        coords: vec![RevisionCoordSpec {
            id: "x".into(),
            domain_values: vec![ScalarLit::rat(0, 1).unwrap(), ScalarLit::rat(1, 1).unwrap()],
        }],
        background_constraints: vec![],
        sources: vec![SourcePresentationSpec {
            source_id: "s1".into(),
            origin: SourceRef::new("s1", OriginKind::StaticAnalysis),
            assignments: BTreeMap::new(),
            forbidden_values: vec![],
            extra_constraints: vec![],
        }],
        support_goal: Some(SupportGoalSpec {
            trusted_assignments: BTreeMap::new(),
            candidates: vec![CandidateRecordSpec {
                id: "h1".into(),
                coord: "x".into(),
                value: ScalarLit::rat(1, 1).unwrap(),
                cost: Some(ScalarLit::Q {
                    num: num_bigint::BigInt::from(2),
                    den: num_bigint::BigInt::from(4),
                }),
                origin: SourceRef::new("c1", OriginKind::LlmCandidate),
                verified_actual_value: None,
            }],
            goal: SupportGoalFormula::CoordEqualsConst("x".into(), ScalarLit::rat(1, 1).unwrap()),
            expected_truth: true,
            check_post_adoption_stability: false,
        }),
        max_sources_subset_steps: 0,
        max_results: 0,
        provenance: sample_prov(),
        undeclared_unobserved_slots: vec![],
    };
    assert!(matches!(
        validate_multisource_task(unreduced_ms),
        Err(ValidationError::InvalidRational { .. })
    ));

    // 4. open_domain bidirectional equality & carrier checks
    let base_open = OpenDomainSpec {
        substructure_carriers: BTreeMap::from([("A".into(), vec!["a0".into()])]),
        ambient_carriers: BTreeMap::from([("A".into(), vec!["a0".into(), "a1".into()])]),
        substructure_ops: vec![OpenOpTable {
            name: "f".into(),
            arg_sorts: vec!["A".into()],
            out_sort: "A".into(),
            entries: BTreeMap::new(),
        }],
        ambient_ops: vec![OpenOpTable {
            name: "f".into(),
            arg_sorts: vec!["A".into()],
            out_sort: "A".into(),
            entries: BTreeMap::new(),
        }],
        substructure_rels: vec![super::partial::OpenRelTable {
            name: "R".into(),
            arg_sorts: vec!["A".into()],
            entries: BTreeSet::new(),
        }],
        ambient_rels: vec![super::partial::OpenRelTable {
            name: "R".into(),
            arg_sorts: vec!["A".into()],
            entries: BTreeSet::new(),
        }],
        fiber_checks: vec![],
        positive_or_law: PartialEvalLawSpec {
            name: "pos".into(),
            antecedent: None,
            conclusion: PartialFormula::Eq(
                PartialTerm::Const("a0".into()),
                PartialTerm::Const("a0".into()),
            ),
            is_required_law: true,
        },
        affine_restriction: None,
    };
    let make_open_task = |od: OpenDomainSpec| PartialTaskSpec {
        name: "open_neg".into(),
        representation: PartialRepresentation::UnsupportedClass {
            description: "open_only".into(),
        },
        eval_laws: vec![],
        quantifier_spec: None,
        open_domain: Some(od),
        provenance: sample_prov(),
        undeclared_unobserved_slots: vec![],
    };

    let mut amb_only_sort = base_open.clone();
    amb_only_sort
        .ambient_carriers
        .insert("B".into(), vec!["b0".into()]);
    assert!(matches!(
        validate_partial_task(make_open_task(amb_only_sort)),
        Err(ValidationError::UnknownRef {
            kind: "substructure_sort",
            ..
        })
    ));

    let mut amb_only_op = base_open.clone();
    amb_only_op.ambient_ops.push(OpenOpTable {
        name: "g".into(),
        arg_sorts: vec!["A".into()],
        out_sort: "A".into(),
        entries: BTreeMap::new(),
    });
    assert!(matches!(
        validate_partial_task(make_open_task(amb_only_op)),
        Err(ValidationError::UnknownRef {
            kind: "substructure_op",
            ..
        })
    ));

    let mut amb_only_rel = base_open.clone();
    amb_only_rel
        .ambient_rels
        .push(super::partial::OpenRelTable {
            name: "Q".into(),
            arg_sorts: vec!["A".into()],
            entries: BTreeSet::new(),
        });
    assert!(matches!(
        validate_partial_task(make_open_task(amb_only_rel)),
        Err(ValidationError::UnknownRef {
            kind: "substructure_rel",
            ..
        })
    ));

    let mut dup_carrier = base_open.clone();
    dup_carrier
        .ambient_carriers
        .insert("A".into(), vec!["a0".into(), "a0".into()]);
    assert!(matches!(
        validate_partial_task(make_open_task(dup_carrier)),
        Err(ValidationError::DuplicateDecl {
            kind: "open_domain_element",
            ..
        })
    ));

    let mut empty_elem = base_open.clone();
    empty_elem
        .ambient_carriers
        .insert("A".into(), vec!["".into()]);
    assert!(matches!(
        validate_partial_task(make_open_task(empty_elem)),
        Err(ValidationError::EmptyName { .. })
    ));

    // 5. partial term Var binding & identifier non-emptiness checks
    let mut unbound_var = base_open.clone();
    unbound_var.positive_or_law.conclusion = PartialFormula::Eq(
        PartialTerm::Var("unbound".into()),
        PartialTerm::Const("a0".into()),
    );
    assert!(matches!(
        validate_partial_task(make_open_task(unbound_var)),
        Err(ValidationError::UnknownRef {
            kind: "bound_var",
            ..
        })
    ));

    let mut empty_const = base_open.clone();
    empty_const.positive_or_law.conclusion = PartialFormula::Eq(
        PartialTerm::Const("".into()),
        PartialTerm::Const("a0".into()),
    );
    assert!(matches!(
        validate_partial_task(make_open_task(empty_const)),
        Err(ValidationError::EmptyName { .. })
    ));

    let mut let_bound = base_open.clone();
    let_bound.positive_or_law.conclusion = PartialFormula::Eq(
        PartialTerm::Let {
            var: "x".into(),
            bound: Box::new(PartialTerm::Const("a0".into())),
            body: Box::new(PartialTerm::Var("x".into())),
        },
        PartialTerm::Const("a0".into()),
    );
    assert!(validate_partial_task(make_open_task(let_bound)).is_ok());

    let mut empty_var_ref = base_open.clone();
    empty_var_ref.positive_or_law.conclusion =
        PartialFormula::Eq(PartialTerm::Var("".into()), PartialTerm::Const("a0".into()));
    assert!(matches!(
        validate_partial_task(make_open_task(empty_var_ref)),
        Err(ValidationError::EmptyName { .. })
    ));

    let mut empty_let_binder = base_open;
    empty_let_binder.positive_or_law.conclusion = PartialFormula::Eq(
        PartialTerm::Let {
            var: "".into(),
            bound: Box::new(PartialTerm::Const("a0".into())),
            body: Box::new(PartialTerm::Const("a0".into())),
        },
        PartialTerm::Const("a0".into()),
    );
    assert!(matches!(
        validate_partial_task(make_open_task(empty_let_binder)),
        Err(ValidationError::EmptyName { .. })
    ));

    // direction_t 列数が 0 のとき非零 x0 は拒否され、零 x0 は受理される
    use super::partial::AffinePartialPresentation;
    let make_aff = |x0_val: i64| PartialTaskSpec {
        name: "aff_zero_tcols".into(),
        representation: PartialRepresentation::Affine(AffinePartialPresentation {
            coeff_domain: CoeffDomain::Z,
            coord_names: vec!["p".into()],
            x0: vec![ScalarLit::int(x0_val)],
            direction_t: vec![vec![]],
            background_rows: vec![],
            record_rows: vec![],
            eval_equations: vec![],
        }),
        eval_laws: vec![],
        quantifier_spec: None,
        open_domain: None,
        provenance: sample_prov(),
        undeclared_unobserved_slots: vec![],
    };
    assert!(validate_partial_task(make_aff(0)).is_ok());
    assert!(matches!(
        validate_partial_task(make_aff(1)),
        Err(ValidationError::ConversionError { .. })
    ));

    // Affine + 非空 eval_laws は黙殺せず ConversionError で拒否
    use super::occurrence::OccurrenceReadingSpec;
    use super::partial::{PartialFormula as PF, PartialTerm as PT};
    let mut aff_with_laws = make_aff(0);
    aff_with_laws.eval_laws.push(PartialEvalLawSpec {
        name: "l".into(),
        antecedent: None,
        conclusion: PF::Eq(PT::Const("0".into()), PT::Const("0".into())),
        is_required_law: true,
    });
    assert!(matches!(
        validate_partial_task(aff_with_laws),
        Err(ValidationError::ConversionError { .. })
    ));

    // base_readings と explicit_contexts を横断する同名読取りは拒否
    let dup_reading = OccurrenceTaskSpec {
        name: "dup_reading".into(),
        sorts: vec![OccurrenceSortSpec {
            name: "S".into(),
            elements: vec!["a".into()],
            is_fixed_value: false,
        }],
        operations: vec![],
        relations: vec![],
        identity_requests: vec![],
        op_records: vec![],
        pred_records: vec![],
        base_readings: vec![OccurrenceReadingSpec {
            name: "o".into(),
            sort: "S".into(),
            values: BTreeMap::from([("a".into(), Some("0".into()))]),
        }],
        context_closed_17_5: false,
        explicit_contexts: vec![OccurrenceReadingSpec {
            name: "o".into(),
            sort: "S".into(),
            values: BTreeMap::from([("a".into(), Some("1".into()))]),
        }],
        preserve_full_domains: vec![],
        initial_readouts: vec![],
        provenance: sample_prov(),
        max_congruence_steps: 0,
        max_partitions: 0,
        undeclared_unobserved_slots: vec![],
    };
    assert!(matches!(
        validate_occurrence_task(dup_reading),
        Err(ValidationError::DuplicateDecl { .. })
    ));
}
