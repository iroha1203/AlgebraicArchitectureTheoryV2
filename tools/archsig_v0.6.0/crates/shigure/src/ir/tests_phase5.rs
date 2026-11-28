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
    let _ = BTreeSet::<String>::new();
}
