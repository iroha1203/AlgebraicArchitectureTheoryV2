//! `shigure_robustness` ソルバの網羅単体テスト（AC3・AC6・W4・W6・P7）。

use crate::ir::change::{ChangeSpec, EditableTarget, NamedPoly, ParamDecl, PointDomain};
use crate::ir::family::{
    CandidateFamilySpec, CandidateMember, CandidateSpace, FamilySpec, GoodnessKind, GoodnessSpec,
    PreservationGoodnessSource, RawSequenceCheck, ReadingComparisonSpec, RealizationFamilySpec,
    RealizationMember, RealizationSpace,
};
use crate::ir::presentation::{
    ComparisonPair, CoordDecl, CoordValue, ObservationDecl, OperationDecl, PhaseDecl, Presentation,
    SortDecl, StateComparison, TranslatedStep, TranslatedWord, WordTranslation,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::robustness::{CandidateSelector, CheckedRobustnessTask, RobustnessTaskSpec};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::solver::solve_robustness_task;
use std::collections::BTreeMap;

fn src(id: &str, kind: OriginKind) -> SourceRef {
    SourceRef::new(id, kind)
}

fn q(n: i64) -> ScalarLit {
    ScalarLit::rat(n, 1).expect("integer rational")
}

fn fp(val: u32, p: u32) -> ScalarLit {
    ScalarLit::Fp {
        value: val.into(),
        modulus: p.into(),
    }
}

fn w4_family_with_eq(eq: PolyExpr) -> FamilySpec {
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
                    assignments: BTreeMap::from([("u".to_owned(), CoordValue::Observed(q(0)))]),
                    is_raw_candidate: false,
                    presentation: None,
                    origin: src("obs-u0", OriginKind::StaticAnalysis),
                },
                RealizationMember {
                    id: "u1".to_owned(),
                    assignments: BTreeMap::from([("u".to_owned(), CoordValue::Observed(q(1)))]),
                    is_raw_candidate: false,
                    presentation: None,
                    origin: src("obs-u1", OriginKind::RuntimeObservation),
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
                    assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(0)))]),
                    origin: src("cand-c0", OriginKind::HumanAdopted),
                },
                CandidateMember {
                    id: "c1".to_owned(),
                    assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(1)))]),
                    origin: src("cand-c1", OriginKind::LlmCandidate),
                },
            ]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new("ok", eq)],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: Provenance::new(
            vec![src("fam-w4", OriginKind::HumanAdopted)],
            vec![MathClause::G140E3, MathClause::G142G2],
        ),
    }
}

#[test]
fn robustness_w4_separates_designated_pointwise_and_common_quantifiers() {
    // Diagonal u - c = 0: pointwise forall u exists c holds, common exists c forall u fails.
    let fam = w4_family_with_eq(PolyExpr::diff(PolyExpr::param("u"), PolyExpr::param("c")));
    let task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "w4_diag".to_owned(),
        family: fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        designated_candidate: Some(CandidateSelector::ById("c0".to_owned())),
        check_universal_ring: false,
        fine_base_value: None,
        provenance: Provenance::new(vec![], vec![MathClause::G140E4, MathClause::G142G2]),
    })
    .unwrap();

    let out = solve_robustness_task(&task);
    assert_eq!(out.verdict, Verdict::Refuted);
    let det = out.robustness.as_ref().expect("robustness detail");
    assert_eq!(det.goodness_kind, GoodnessKind::Direct);
    assert!(det.fiber_non_empty.non_empty);
    assert_eq!(det.fiber_non_empty.status, "non_empty");

    let vd = det.valid_designated.as_ref().expect("valid_designated");
    assert!(!vd.satisfied);
    assert!(!vd.vacuously_true_empty_fiber);
    assert_eq!(vd.supporting_witnesses.len(), 1);
    assert!(vd.counterexample.is_some());

    let pw = det.pointwise.as_ref().expect("pointwise");
    assert!(pw.satisfied);
    assert!(!pw.vacuously_true_empty_fiber);
    assert_eq!(pw.witnesses.len(), 2);
    assert!(pw.counterexample.is_none());

    let cm = det.common_candidate.as_ref().expect("common");
    assert!(!cm.satisfied);
    assert!(!cm.vacuously_true_empty_fiber);
    assert!(cm.candidate_assignments.is_none());
    assert_eq!(cm.counterexample_witnesses.len(), 2);

    // Zero-product equation (u - c) * c = 0: c0 = 0 works for ALL realizations.
    let fam_common = w4_family_with_eq(PolyExpr::prod(
        PolyExpr::diff(PolyExpr::param("u"), PolyExpr::param("c")),
        PolyExpr::param("c"),
    ));
    let task_common = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "w4_common_ok".to_owned(),
        family: fam_common,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    let out_ok = solve_robustness_task(&task_common);
    assert_eq!(out_ok.verdict, Verdict::Established);
    let cm_ok = out_ok.robustness.unwrap().common_candidate.unwrap();
    assert!(cm_ok.satisfied);
    assert_eq!(cm_ok.candidate_id.as_deref(), Some("c0"));
    assert_eq!(
        cm_ok.candidate_assignments,
        Some(BTreeMap::from([("c".to_owned(), "0".to_owned())]))
    );
}

#[test]
fn robustness_empty_fiber_marks_vacuous_truth_but_refutes_overall() {
    let fam = FamilySpec {
        name: "EmptyFiber".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["u".to_owned()],
            b_vars: vec!["b".to_owned()],
            reading_q: vec![PolyExpr::param("u")],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![NamedPoly::new(
                    "unit",
                    PolyExpr::diff(PolyExpr::param("u"), PolyExpr::rat(1, 1).unwrap()),
                )],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: src("scheme-u", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec!["c".to_owned()],
            pi: vec![PolyExpr::param("c")],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".to_owned(),
                assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(0)))]),
                origin: src("cand-c0", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };

    let task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "empty_fiber".to_owned(),
        family: fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![q(0)],
        designated_candidate: Some(CandidateSelector::ById("c0".to_owned())),
        check_universal_ring: false,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();

    let out = solve_robustness_task(&task);
    assert_eq!(out.verdict, Verdict::Refuted);
    let det = out.robustness.as_ref().expect("robustness detail");
    assert!(!det.fiber_non_empty.non_empty);
    assert_eq!(det.fiber_non_empty.status, "empty_realizations");
    assert!(det.fiber_non_empty.empty_witness.is_some());
    assert!(
        det.valid_designated
            .as_ref()
            .unwrap()
            .vacuously_true_empty_fiber
    );
    assert!(det.pointwise.as_ref().unwrap().vacuously_true_empty_fiber);
    assert!(
        det.common_candidate
            .as_ref()
            .unwrap()
            .vacuously_true_empty_fiber
    );
}

#[test]
fn robustness_existential_restores_witness_with_reeval_or_emits_empty_witness() {
    let shift_pres = |name: &str, coeff_expr: PolyExpr| Presentation {
        name: name.to_owned(),
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
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "step".to_owned(),
            source_phase: "Active".to_owned(),
            target_phase: "Active".to_owned(),
            args: vec![],
            domain_laws: vec![],
            updates: BTreeMap::from([(
                "x".to_owned(),
                PolyExpr::sum(PolyExpr::state("x"), coeff_expr),
            )]),
            provenance: None,
        }],
        observations: vec![ObservationDecl {
            name: "obs".to_owned(),
            phase: "Active".to_owned(),
            components: vec![PolyExpr::state("x")],
            provenance: None,
        }],
        provenance: Provenance::default(),
    };

    let fam = FamilySpec {
        name: "ExistShift".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["u".to_owned()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::FiniteMembers(vec![
                RealizationMember {
                    id: "u_solvable".to_owned(),
                    assignments: BTreeMap::from([("u".to_owned(), CoordValue::Observed(q(2)))]),
                    is_raw_candidate: false,
                    presentation: None,
                    origin: src("u-solv", OriginKind::StaticAnalysis),
                },
                RealizationMember {
                    id: "u_blocked".to_owned(),
                    assignments: BTreeMap::from([("u".to_owned(), CoordValue::Observed(q(0)))]),
                    is_raw_candidate: false,
                    presentation: None,
                    origin: src("u-blk", OriginKind::StaticAnalysis),
                },
            ]),
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec!["c".to_owned()],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c1".to_owned(),
                assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(6)))]),
                origin: src("c1", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Existential {
            witness_vars: vec!["w".to_owned()],
            // Wait: u * w - c = 0 solvable iff u != 0 (for c = 6: w = 3 at u = 2, empty at u = 0).
            equations: vec![NamedPoly::new(
                "lin",
                PolyExpr::diff(
                    PolyExpr::prod(PolyExpr::param("u"), PolyExpr::param("w")),
                    PolyExpr::param("c"),
                ),
            )],
            invertibles: vec![],
            preservation: Some(PreservationGoodnessSource {
                pair: ComparisonPair {
                    before: shift_pres("Before", PolyExpr::rat(3, 1).unwrap()),
                    after: shift_pres("After", PolyExpr::param("p")),
                    state_comparisons: vec![StateComparison {
                        after_phase: "Active".to_owned(),
                        before_phase: "Active".to_owned(),
                        map: BTreeMap::from([("x".to_owned(), PolyExpr::state("x"))]),
                        provenance: None,
                    }],
                    word_translation: WordTranslation {
                        entries: vec![TranslatedWord {
                            after_operation: "step".to_owned(),
                            steps: vec![TranslatedStep {
                                before_operation: "step".to_owned(),
                                arg_exprs: vec![],
                            }],
                            provenance: None,
                        }],
                    },
                },
                change_spec: ChangeSpec {
                    name: "H".to_owned(),
                    coeff_domain: CoeffDomain::Q,
                    parameters: vec![ParamDecl {
                        name: "p".to_owned(),
                        coeff_domain: CoeffDomain::Q,
                        provenance: None,
                    }],
                    fixed: vec![],
                    editable: vec![EditableTarget::OperationExpr {
                        presentation: "After".to_owned(),
                        operation: "step".to_owned(),
                    }],
                    provenance: Provenance::default(),
                },
                param_bindings: BTreeMap::from([("p".to_owned(), PolyExpr::param("w"))]),
            }),
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };

    let task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "exist_restore".to_owned(),
        family: fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        designated_candidate: Some(CandidateSelector::ById("c1".to_owned())),
        check_universal_ring: false,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();

    let out = solve_robustness_task(&task);
    assert_eq!(out.verdict, Verdict::Refuted);
    let vd = out.robustness.unwrap().valid_designated.unwrap();
    assert!(!vd.satisfied);
    assert_eq!(vd.supporting_witnesses.len(), 1);
    let pass_w = &vd.supporting_witnesses[0];
    assert!(pass_w.passed);
    assert_eq!(pass_w.legal_execution_exists, Some(true));
    let restored = pass_w
        .restored_completion
        .as_ref()
        .expect("restored witness");
    assert_eq!(
        restored.witness_assignments.get("w").map(String::as_str),
        Some("3")
    );
    assert!(restored.reeval.checked && restored.reeval.matched);
    assert!(restored.restored_artifact.is_some());

    let fail_w = vd.counterexample.as_ref().expect("counterexample at u=0");
    assert!(!fail_w.passed);
    assert_eq!(fail_w.legal_execution_exists, Some(false));
    assert!(fail_w.empty_witness.is_some());
    assert!(fail_w.restored_completion.is_none());
}

#[test]
fn robustness_universal_ring_refutes_fp_frobenius_and_w6_dual_number() {
    // Part A: F_5 has u^5 - u = 0 for every point u in F_5, but R = F_5[u] fails u^5 - u = 0.
    let fp_fam = FamilySpec {
        name: "FpFrob".to_owned(),
        coeff_domain: CoeffDomain::Fp(5u32.into()),
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["u".to_owned()],
            b_vars: vec!["b".to_owned()],
            reading_q: vec![PolyExpr::constant(fp(0, 5))],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: src("fp-u", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec!["c".to_owned()],
            pi: vec![PolyExpr::param("c")],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".to_owned(),
                assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(fp(0, 5)))]),
                origin: src("fp-c0", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new(
                "fermat",
                PolyExpr::diff(PolyExpr::pow(PolyExpr::param("u"), 5), PolyExpr::param("u")),
            )],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };
    let fp_task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "fp5_rob".to_owned(),
        family: fp_fam,
        point_domain: PointDomain::FiniteFieldPoints(5u32.into()),
        base_value: vec![fp(0, 5)],
        designated_candidate: Some(CandidateSelector::ById("c0".to_owned())),
        check_universal_ring: true,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    let fp_out = solve_robustness_task(&fp_task);
    assert_eq!(fp_out.verdict, Verdict::Refuted);
    let fp_det = fp_out.robustness.unwrap();
    assert!(fp_det.valid_designated.unwrap().satisfied);
    assert!(fp_det.common_candidate.unwrap().satisfied);
    let ur_fp = fp_det.universal_ring.expect("universal ring evaluated");
    assert_eq!(ur_fp.stable, Some(false));
    assert!(
        ur_fp
            .counterexample_ring
            .as_deref()
            .unwrap_or("")
            .contains("Fp(5)")
    );
    assert!(!ur_fp.counterexample_residuals.is_empty());

    // Part B: W6 nilpotent dual-number witness: (rho - 1)^2 = 0 passes all closed field points (rho=1)
    // yet fails on Q[eps]/(eps^2) at rho = 1 + eps because (rho - 1) = eps != 0.
    let rho_minus_1 = PolyExpr::diff(PolyExpr::param("rho"), PolyExpr::rat(1, 1).unwrap());
    let w6_fam = FamilySpec {
        name: "W6Dual".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["rho".to_owned()],
            b_vars: vec!["b".to_owned()],
            reading_q: vec![PolyExpr::pow(rho_minus_1.clone(), 2)],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: src("w6-u", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec!["c".to_owned()],
            pi: vec![PolyExpr::param("c")],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".to_owned(),
                assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(0)))]),
                origin: src("w6-c0", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new("unipotent_trivial", rho_minus_1)],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };
    let w6_task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "w6_dual".to_owned(),
        family: w6_fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![q(0)],
        designated_candidate: Some(CandidateSelector::ById("c0".to_owned())),
        check_universal_ring: true,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    let w6_out = solve_robustness_task(&w6_task);
    assert_eq!(w6_out.verdict, Verdict::Refuted);
    let w6_det = w6_out.robustness.unwrap();
    assert!(w6_det.valid_designated.unwrap().satisfied);
    let ur_w6 = w6_det.universal_ring.expect("W6 universal ring");
    assert_eq!(ur_w6.stable, Some(false));
    let dual = ur_w6
        .dual_number_counterexample
        .expect("dual number counterexample");
    assert!(dual.assignments.values().any(|v| v.contains("eps")));
    assert!(dual.nonzero_residuals.iter().any(|r| r.contains("eps")));
}

#[test]
fn robustness_reading_comparison_and_p7_raw_sequence_residuals() {
    let make_raw_pres = |name: &str, lose_on_finish: bool| Presentation {
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
                updates: BTreeMap::from([(
                    "B".to_owned(),
                    if lose_on_finish {
                        PolyExpr::rat(0, 1).unwrap()
                    } else {
                        PolyExpr::state("B")
                    },
                )]),
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
    };

    let fam = FamilySpec {
        name: "P7Ledger".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["x".to_owned(), "y".to_owned()],
            b_vars: vec!["b".to_owned()],
            reading_q: vec![PolyExpr::sum(PolyExpr::param("x"), PolyExpr::param("y"))],
            space: RealizationSpace::FiniteMembers(vec![
                RealizationMember {
                    id: "raw_good".to_owned(),
                    assignments: BTreeMap::from([
                        ("x".to_owned(), CoordValue::Observed(q(1))),
                        ("y".to_owned(), CoordValue::Observed(q(0))),
                    ]),
                    is_raw_candidate: false,
                    presentation: Some(make_raw_pres("M_good", false)),
                    origin: src("raw-good", OriginKind::StaticAnalysis),
                },
                RealizationMember {
                    id: "raw_bad".to_owned(),
                    assignments: BTreeMap::from([
                        ("x".to_owned(), CoordValue::Observed(q(0))),
                        ("y".to_owned(), CoordValue::Observed(q(1))),
                    ]),
                    is_raw_candidate: true,
                    presentation: Some(make_raw_pres("M_bad", true)),
                    origin: src("raw-bad", OriginKind::LlmCandidate),
                },
            ]),
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec!["c".to_owned()],
            pi: vec![PolyExpr::param("c")],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c1".to_owned(),
                assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(1)))]),
                origin: src("cand-c1", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![],
            invertibles: vec![],
            preservation: None,
            raw_sequence: Some(RawSequenceCheck {
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
            }),
        },
        reading_comparison: Some(ReadingComparisonSpec {
            name: "coarse_vs_fine".to_owned(),
            fine_b_vars: vec!["fx".to_owned(), "fy".to_owned()],
            fine_q: vec![PolyExpr::param("x"), PolyExpr::param("y")],
            coarsen_r: vec![PolyExpr::sum(PolyExpr::param("fx"), PolyExpr::param("fy"))],
            provenance: Provenance::default(),
        }),
        provenance: Provenance::default(),
    };

    let task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "p7_compare".to_owned(),
        family: fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![q(1)],
        designated_candidate: Some(CandidateSelector::ById("c1".to_owned())),
        check_universal_ring: false,
        fine_base_value: Some(vec![q(1), q(0)]),
        provenance: Provenance::default(),
    })
    .unwrap();

    let out = solve_robustness_task(&task);
    assert_eq!(out.verdict, Verdict::Refuted);
    let rc = out
        .robustness
        .unwrap()
        .reading_comparison
        .expect("reading comparison");
    assert!(rc.commutativity_verified);
    assert!(!rc.coarse_robust);
    assert!(rc.fine_robust);
    assert!(rc.coarse_implies_fine_preserved);
    assert!(rc.reverse_implication_not_claimed);
    assert!(rc.fine_only_counterexample.is_some());
    assert_eq!(rc.raw_candidate_evaluations.len(), 2);
    let good_eval = rc
        .raw_candidate_evaluations
        .iter()
        .find(|e| e.member_id == "raw_good")
        .unwrap();
    assert!(good_eval.passed);
    assert_eq!(good_eval.legal_execution_exists, Some(true));
    assert!(good_eval.residuals.is_empty());

    let bad_eval = rc
        .raw_candidate_evaluations
        .iter()
        .find(|e| e.member_id == "raw_bad")
        .unwrap();
    assert!(!bad_eval.passed);
    assert_eq!(bad_eval.legal_execution_exists, Some(true));
    assert_eq!(bad_eval.residuals, vec!["read[0]_diff = -1"]);
}

#[test]
fn robustness_silences_fail_closed_on_unobserved_and_nonlinear_q_existence() {
    // 1. Unobserved dependency -> Verdict::Undetermined
    let mut unobs_fam =
        w4_family_with_eq(PolyExpr::diff(PolyExpr::param("u"), PolyExpr::param("c")));
    if let RealizationSpace::FiniteMembers(ref mut ms) = unobs_fam.realizations.space {
        ms[0]
            .assignments
            .insert("u".to_owned(), CoordValue::Missing);
    }
    let unobs_task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "unobs_rob".to_owned(),
        family: unobs_fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    let unobs_out = solve_robustness_task(&unobs_task);
    assert!(matches!(
        unobs_out.verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { .. })
    ));

    // 2. Nonlinear multivariate realization scheme over RationalPoints -> Undetermined
    let nl_fam = FamilySpec {
        name: "NonlinQ".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["u".to_owned(), "v".to_owned()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![NamedPoly::new(
                    "prod2",
                    PolyExpr::diff(
                        PolyExpr::prod(PolyExpr::param("u"), PolyExpr::param("v")),
                        PolyExpr::rat(2, 1).unwrap(),
                    ),
                )],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: src("nl-u", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec!["c".to_owned()],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".to_owned(),
                assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(0)))]),
                origin: src("nl-c", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };
    let nl_task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "nonlin_q".to_owned(),
        family: nl_fam,
        point_domain: PointDomain::RationalPoints,
        base_value: vec![],
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    let nl_out = solve_robustness_task(&nl_task);
    assert!(matches!(
        nl_out.verdict,
        Verdict::Undetermined(SilenceReason::NonLinearRationalOrIntegerExistence { .. })
    ));
}

#[test]
fn robustness_symbolic_closure_quantifiers_and_projection_order() {
    // 1. U = A^1(u), C = A^1(c), E_ok: u - c = 0 over AlgebraicClosure -> pointwise true, common false.
    let make_sym = |eq: PolyExpr| FamilySpec {
        name: "SymUC".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["u".to_owned()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: src("sym-u", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec!["c".to_owned()],
            pi: vec![],
            space: CandidateSpace::PolynomialScheme {
                equations: vec![],
                invertibles: vec![],
                origin: src("sym-c", OriginKind::HumanAdopted),
            },
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new("ok", eq)],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };

    let diag_task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "sym_diag".to_owned(),
        family: make_sym(PolyExpr::diff(PolyExpr::param("u"), PolyExpr::param("c"))),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    let diag_out = solve_robustness_task(&diag_task);
    assert_eq!(diag_out.verdict, Verdict::Refuted);
    let diag_det = diag_out.robustness.unwrap();
    assert!(diag_det.pointwise.unwrap().satisfied);
    let diag_cm = diag_det.common_candidate.unwrap();
    assert!(!diag_cm.satisfied);
    assert!(diag_cm.candidate_assignments.is_none());

    // 2. E_ok: c * (u - c) = 0 -> common c = 0 works for ALL u in A^1!
    let prod_task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "sym_common".to_owned(),
        family: make_sym(PolyExpr::prod(
            PolyExpr::param("c"),
            PolyExpr::diff(PolyExpr::param("u"), PolyExpr::param("c")),
        )),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    let prod_out = solve_robustness_task(&prod_task);
    assert_eq!(prod_out.verdict, Verdict::Established);
    let prod_det = prod_out.robustness.unwrap();
    assert!(prod_det.pointwise.unwrap().satisfied);
    let prod_cm = prod_det.common_candidate.unwrap();
    assert!(prod_cm.satisfied);
    assert_eq!(
        prod_cm.candidate_assignments,
        Some(BTreeMap::from([("c".to_owned(), "0".to_owned())]))
    );
}
