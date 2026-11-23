use super::*;
use crate::ir::change::{
    ChangeSpec, EditableTarget, FixedTarget, NamedPoly, ParamDecl, PointDomain,
};
use crate::ir::family::{
    CandidateFamilySpec, CandidateMember, CandidateSpace, CheckedFamilySpec, FamilySpec,
    GoodnessSpec, PreservationGoodnessSource, RawSequenceCheck, ReadingComparisonSpec,
    RealizationFamilySpec, RealizationMember, RealizationSpace,
};
use crate::ir::presentation::{
    ComparisonPair, CoordDecl, CoordValue, ObservationDecl, OperationDecl, PhaseDecl, Presentation,
    SortDecl, StateComparison, TranslatedStep, TranslatedWord, WordTranslation,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::robustness::{
    CandidateSelector, CheckedChevalleyTask, CheckedRobustnessTask, ChevalleyTaskSpec,
    RationalFiberProbe, RobustnessTaskSpec,
};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use std::collections::BTreeMap;

fn src(id: &str, kind: OriginKind) -> SourceRef {
    SourceRef::new(id, kind)
}

fn prov(id: &str, clause: MathClause) -> Provenance {
    Provenance::new(vec![src(id, OriginKind::HumanAdopted)], vec![clause])
}

fn q_lit(n: i64) -> ScalarLit {
    ScalarLit::rat(n, 1).expect("denominator 1 is valid")
}

fn q_expr(n: i64) -> PolyExpr {
    PolyExpr::constant(q_lit(n))
}

#[test]
fn rf1_existential_preservation_rational_points_fails_closed_without_witness() {
    let orig = src("orig-rf1", OriginKind::HumanAdopted);
    let mk_pres = |name: &str| Presentation {
        name: name.into(),
        coeff_domain: CoeffDomain::Q,
        sorts: vec![SortDecl {
            name: "S".into(),
            rank: 1,
            coeff_domain: CoeffDomain::Q,
            provenance: Some(orig.clone()),
        }],
        phases: vec![PhaseDecl {
            name: "Idle".into(),
            coords: vec![CoordDecl::symbolic("x", "S")],
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "step".into(),
            source_phase: "Idle".into(),
            target_phase: "Idle".into(),
            args: vec![],
            domain_laws: vec![],
            updates: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
            provenance: None,
        }],
        observations: vec![ObservationDecl {
            name: "read".into(),
            phase: "Idle".into(),
            components: vec![PolyExpr::state("x")],
            provenance: None,
        }],
        provenance: prov("orig-pres", MathClause::G140P3P5),
    };
    let pair = ComparisonPair {
        before: mk_pres("Rf1Before"),
        after: mk_pres("Rf1After"),
        state_comparisons: vec![StateComparison {
            after_phase: "Idle".into(),
            before_phase: "Idle".into(),
            map: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
            provenance: None,
        }],
        word_translation: WordTranslation {
            entries: vec![TranslatedWord {
                after_operation: "step".into(),
                steps: vec![TranslatedStep {
                    before_operation: "step".into(),
                    arg_exprs: vec![],
                }],
                provenance: None,
            }],
        },
    };
    let change_spec = ChangeSpec {
        name: "Rf1Change".into(),
        coeff_domain: CoeffDomain::Q,
        parameters: vec![
            ParamDecl {
                name: "w1".into(),
                coeff_domain: CoeffDomain::Q,
                provenance: None,
            },
            ParamDecl {
                name: "w2".into(),
                coeff_domain: CoeffDomain::Q,
                provenance: None,
            },
        ],
        fixed: vec![
            FixedTarget::StateComparisonExpr {
                after_phase: "Idle".into(),
            },
            FixedTarget::WordTranslationOp {
                operation: "step".into(),
            },
        ],
        editable: vec![EditableTarget::OperationExpr {
            presentation: "Rf1After".into(),
            operation: "step".into(),
        }],
        provenance: prov("orig-chg", MathClause::G140E1E2),
    };

    // Invertibles exclude diagonal (w1 == w2) and all off-diagonal sample digits for w1 in {-3..3, 5}
    let mut off_diag_excluder = PolyExpr::diff(PolyExpr::param("w1"), q_expr(0));
    for v in [1, -1, 2, -2, 3, -3, 5] {
        off_diag_excluder = PolyExpr::prod(
            off_diag_excluder,
            PolyExpr::diff(PolyExpr::param("w1"), q_expr(v)),
        );
    }

    let fam = FamilySpec {
        name: "rf1_fam".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u".into(),
            u_vars: vec!["u".into()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::FiniteMembers(vec![RealizationMember {
                id: "u0".into(),
                assignments: BTreeMap::from([("u".into(), CoordValue::Observed(q_lit(0)))]),
                is_raw_candidate: false,
                presentation: None,
                origin: src("orig-u0", OriginKind::StaticAnalysis),
            }]),
        },
        candidates: CandidateFamilySpec {
            name: "c".into(),
            c_vars: vec!["c".into()],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".into(),
                assignments: BTreeMap::from([("c".into(), CoordValue::Observed(q_lit(0)))]),
                origin: src("orig-c0", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Existential {
            witness_vars: vec!["w1".into(), "w2".into()],
            equations: vec![],
            invertibles: vec![
                NamedPoly::new(
                    "not_diag",
                    PolyExpr::diff(PolyExpr::param("w1"), PolyExpr::param("w2")),
                ),
                NamedPoly::new("skip_sample_grid", off_diag_excluder),
            ],
            preservation: Some(PreservationGoodnessSource {
                pair,
                change_spec,
                param_bindings: BTreeMap::from([
                    ("w1".into(), PolyExpr::param("w1")),
                    ("w2".into(), PolyExpr::param("w2")),
                ]),
            }),
        },
        reading_comparison: None,
        provenance: prov("orig-fam", MathClause::G141D4),
    };

    let task_q = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "rf1_rational_points".into(),
        family: fam.clone(),
        point_domain: PointDomain::RationalPoints,
        base_value: vec![],
        designated_candidate: Some(CandidateSelector::ById("c0".into())),
        check_universal_ring: false,
        fine_base_value: None,
        provenance: prov("orig-task", MathClause::G141D4),
    })
    .expect("task validates");
    let out_q = solve_robustness_task(&task_q);
    assert!(
        matches!(
            out_q.verdict,
            Verdict::Undetermined(SilenceReason::NonLinearRationalOrIntegerExistence {
                point_domain: PointDomain::RationalPoints,
                ..
            })
        ),
        "expected Undetermined over RationalPoints when no Q witness found, got {:?}",
        out_q.verdict
    );

    // Over AlgebraicClosure, non-empty constructible locus can still establish geometrically.
    let task_bar = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "rf1_algebraic_closure".into(),
        family: fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        designated_candidate: Some(CandidateSelector::ById("c0".into())),
        check_universal_ring: false,
        fine_base_value: None,
        provenance: prov("orig-task", MathClause::G141D5),
    })
    .expect("closure task validates");
    let out_bar = solve_robustness_task(&task_bar);
    assert_eq!(out_bar.verdict, Verdict::Established);
}

#[test]
fn rf2_zero_dim_empty_finite_members_vs_singleton_scheme_consistent() {
    let mk_zero_dim_fam = |cand_space: CandidateSpace| FamilySpec {
        name: "rf2_zero_dim".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u".into(),
            u_vars: vec!["u".into()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::FiniteMembers(vec![RealizationMember {
                id: "u0".into(),
                assignments: BTreeMap::from([("u".into(), CoordValue::Observed(q_lit(1)))]),
                is_raw_candidate: false,
                presentation: None,
                origin: src("orig-u0", OriginKind::StaticAnalysis),
            }]),
        },
        candidates: CandidateFamilySpec {
            name: "c".into(),
            c_vars: vec![],
            pi: vec![],
            space: cand_space,
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new(
                "u_eq_1",
                PolyExpr::diff(PolyExpr::param("u"), q_expr(1)),
            )],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: prov("orig-fam", MathClause::G142G7),
    };

    // 1. FiniteMembers(vec![]) with c_vars = [] is EMPTY candidate space everywhere.
    let empty_fam = mk_zero_dim_fam(CandidateSpace::FiniteMembers(vec![]));
    let chev_empty = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "rf2_empty_chev".into(),
        family: empty_fam.clone(),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: None,
        designated_candidate: None,
        rational_fiber_probes: vec![RationalFiberProbe {
            name: "p0".into(),
            u_assignments: BTreeMap::from([("u".into(), q_lit(1))]),
            c_assignments: BTreeMap::new(),
        }],
        check_global_regular_section: false,
        check_universal_ring: true,
        provenance: prov("orig-chev", MathClause::G142G7),
    })
    .unwrap();
    let out_chev_empty = solve_chevalley_task(&chev_empty);
    assert_eq!(out_chev_empty.verdict, Verdict::Refuted);
    let det_empty = out_chev_empty.chevalley.as_ref().unwrap();
    assert!(det_empty.robust_all_pass.is_empty);
    assert_eq!(det_empty.rational_fiber_probes[0].verdict, Verdict::Refuted);
    let ur_empty = det_empty.universal_ring_contrast.as_ref().unwrap();
    assert!(!ur_empty.evaluated);
    assert!(matches!(
        ur_empty.silence_reason,
        Some(SilenceReason::UniversalRingOutOfScope { .. })
    ));

    let rob_empty = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "rf2_empty_rob".into(),
        family: empty_fam,
        point_domain: PointDomain::RationalPoints,
        base_value: vec![],
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: None,
        provenance: prov("orig-rob", MathClause::G142G2),
    })
    .unwrap();
    assert_eq!(solve_robustness_task(&rob_empty).verdict, Verdict::Refuted);

    // 2. Singleton scheme PolynomialScheme { [], [] } with c_vars = [] is singleton {()}.
    let singleton_fam = mk_zero_dim_fam(CandidateSpace::PolynomialScheme {
        equations: vec![],
        invertibles: vec![],
        origin: src("orig-c-singleton", OriginKind::StaticAnalysis),
    });
    let chev_singleton = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "rf2_singleton_chev".into(),
        family: singleton_fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: None,
        designated_candidate: None,
        rational_fiber_probes: vec![RationalFiberProbe {
            name: "p0".into(),
            u_assignments: BTreeMap::from([("u".into(), q_lit(1))]),
            c_assignments: BTreeMap::new(),
        }],
        check_global_regular_section: false,
        check_universal_ring: true,
        provenance: prov("orig-chev", MathClause::G142G7),
    })
    .unwrap();
    let out_singleton = solve_chevalley_task(&chev_singleton);
    assert_eq!(out_singleton.verdict, Verdict::Established);
    let det_s = out_singleton.chevalley.as_ref().unwrap();
    assert!(!det_s.robust_all_pass.is_empty);
    assert_eq!(det_s.rational_fiber_probes[0].verdict, Verdict::Established);

    // 3. RawSequence Chevalley with c_vars = [] and FiniteMembers(vec![]) must also be Refuted (empty C).
    let orig = src("orig-raw", OriginKind::RuntimeObservation);
    let pres = Presentation {
        name: "Rf2RawPres".into(),
        coeff_domain: CoeffDomain::Q,
        sorts: vec![SortDecl {
            name: "S".into(),
            rank: 1,
            coeff_domain: CoeffDomain::Q,
            provenance: Some(orig.clone()),
        }],
        phases: vec![PhaseDecl {
            name: "S0".into(),
            coords: vec![CoordDecl::symbolic("x", "S")],
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "nop".into(),
            source_phase: "S0".into(),
            target_phase: "S0".into(),
            args: vec![],
            domain_laws: vec![],
            updates: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
            provenance: None,
        }],
        observations: vec![ObservationDecl {
            name: "obs".into(),
            phase: "S0".into(),
            components: vec![PolyExpr::state("x")],
            provenance: None,
        }],
        provenance: prov("orig-pres", MathClause::G140P7),
    };
    let raw_empty_c_fam = FamilySpec {
        name: "rf2_raw_empty_c".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u".into(),
            u_vars: vec!["u".into()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::FiniteMembers(vec![RealizationMember {
                id: "u0".into(),
                assignments: BTreeMap::from([("u".into(), CoordValue::Observed(q_lit(0)))]),
                is_raw_candidate: false,
                presentation: Some(pres),
                origin: orig,
            }]),
        },
        candidates: CandidateFamilySpec {
            name: "c".into(),
            c_vars: vec![],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![],
            invertibles: vec![],
            preservation: None,
            raw_sequence: Some(RawSequenceCheck {
                start_phase: "S0".into(),
                start_state: BTreeMap::from([("x".into(), q_lit(0))]),
                steps: vec![("nop".into(), vec![])],
                observation_name: "obs".into(),
                baseline_step_index: None,
                provenance: prov("orig-seq", MathClause::G140P7),
            }),
        },
        reading_comparison: None,
        provenance: prov("orig-fam", MathClause::G140P7),
    };
    let chev_raw = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "rf2_raw_empty".into(),
        family: raw_empty_c_fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: None,
        designated_candidate: None,
        rational_fiber_probes: vec![],
        check_global_regular_section: false,
        check_universal_ring: false,
        provenance: prov("orig-chev", MathClause::G142G7),
    })
    .unwrap();
    assert_eq!(solve_chevalley_task(&chev_raw).verdict, Verdict::Refuted);
}

#[test]
fn rf3_reading_comparison_uses_winning_common_candidate_not_cs0() {
    let mk_fam = |cand_space: CandidateSpace| FamilySpec {
        name: "rf3_common_eval".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u".into(),
            u_vars: vec!["u".into()],
            b_vars: vec!["b".into()],
            reading_q: vec![q_expr(0)],
            space: RealizationSpace::FiniteMembers(vec![RealizationMember {
                id: "u1".into(),
                assignments: BTreeMap::from([("u".into(), CoordValue::Observed(q_lit(1)))]),
                is_raw_candidate: false,
                presentation: None,
                origin: src("orig-u1", OriginKind::StaticAnalysis),
            }]),
        },
        candidates: CandidateFamilySpec {
            name: "c".into(),
            c_vars: vec!["c".into()],
            pi: vec![q_expr(0)],
            space: cand_space,
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new(
                "u_eq_c",
                PolyExpr::diff(PolyExpr::param("u"), PolyExpr::param("c")),
            )],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: Some(ReadingComparisonSpec {
            name: "rc".into(),
            fine_b_vars: vec!["bf".into()],
            fine_q: vec![PolyExpr::param("u")],
            coarsen_r: vec![q_expr(0)],
            provenance: prov("orig-rc", MathClause::G142G4),
        }),
        provenance: prov("orig-fam", MathClause::G142G4),
    };

    // 1. FiniteMembers [c0=0 (fail), c1=1 (pass)]: designated=None must evaluate c1 (passed == true)
    let t_fin = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "rf3_fin".into(),
        family: mk_fam(CandidateSpace::FiniteMembers(vec![
            CandidateMember {
                id: "c0_fail".into(),
                assignments: BTreeMap::from([("c".into(), CoordValue::Observed(q_lit(0)))]),
                origin: src("orig-c0", OriginKind::HumanAdopted),
            },
            CandidateMember {
                id: "c1_pass".into(),
                assignments: BTreeMap::from([("c".into(), CoordValue::Observed(q_lit(1)))]),
                origin: src("orig-c1", OriginKind::HumanAdopted),
            },
        ])),
        point_domain: PointDomain::RationalPoints,
        base_value: vec![q_lit(0)],
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: None,
        provenance: prov("orig-task", MathClause::G142G4),
    })
    .unwrap();
    let out_fin = solve_robustness_task(&t_fin);
    assert_eq!(out_fin.verdict, Verdict::Established);
    let rc_fin = out_fin
        .robustness
        .as_ref()
        .unwrap()
        .reading_comparison
        .as_ref()
        .unwrap();
    assert!(rc_fin.coarse_robust);
    assert_eq!(rc_fin.raw_candidate_evaluations.len(), 1);
    assert!(
        rc_fin.raw_candidate_evaluations[0].passed,
        "must evaluate winning common candidate c1_pass, not c0_fail"
    );

    // 2. NonFiniteScheme candidate C = A^1_c over AlgebraicClosure with designated=None:
    // common extracts c = 1, so raw_candidate_evaluations must be populated with passed == true.
    let t_scheme = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "rf3_scheme".into(),
        family: mk_fam(CandidateSpace::PolynomialScheme {
            equations: vec![],
            invertibles: vec![],
            origin: src("orig-cs", OriginKind::HumanAdopted),
        }),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![q_lit(0)],
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: None,
        provenance: prov("orig-task", MathClause::G142G4),
    })
    .unwrap();
    let out_scheme = solve_robustness_task(&t_scheme);
    assert_eq!(out_scheme.verdict, Verdict::Established);
    let rc_scheme = out_scheme
        .robustness
        .as_ref()
        .unwrap()
        .reading_comparison
        .as_ref()
        .unwrap();
    assert_eq!(rc_scheme.raw_candidate_evaluations.len(), 1);
    assert!(rc_scheme.raw_candidate_evaluations[0].passed);
}

#[test]
fn rf5_zero_dim_fine_base_and_collision_free_fiber_names() {
    // 1. fine_b_vars = [], fine_base_value = Some(vec![]), coarsen_r = [1] vs base_value = [0]
    let fam_0d = FamilySpec {
        name: "rf5_0d_fine".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u".into(),
            u_vars: vec!["u".into()],
            b_vars: vec!["b".into()],
            reading_q: vec![q_expr(1)],
            space: RealizationSpace::FiniteMembers(vec![RealizationMember {
                id: "u0".into(),
                assignments: BTreeMap::from([("u".into(), CoordValue::Observed(q_lit(0)))]),
                is_raw_candidate: false,
                presentation: None,
                origin: src("orig-u0", OriginKind::StaticAnalysis),
            }]),
        },
        candidates: CandidateFamilySpec {
            name: "c".into(),
            c_vars: vec!["c".into()],
            pi: vec![q_expr(1)],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".into(),
                assignments: BTreeMap::from([("c".into(), CoordValue::Observed(q_lit(0)))]),
                origin: src("orig-c0", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new("ok", q_expr(0))],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: Some(ReadingComparisonSpec {
            name: "rc_0d".into(),
            fine_b_vars: vec![],
            fine_q: vec![],
            coarsen_r: vec![q_expr(1)],
            provenance: prov("orig-rc", MathClause::G140E5Dot1),
        }),
        provenance: prov("orig-fam", MathClause::G140E5Dot1),
    };
    let t_0d = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "rf5_0d_task".into(),
        family: fam_0d,
        point_domain: PointDomain::RationalPoints,
        base_value: vec![q_lit(0)], // r([]) = [1] != [0]
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: Some(vec![]),
        provenance: prov("orig-task", MathClause::G140E5Dot1),
    })
    .unwrap();
    let out_0d = solve_robustness_task(&t_0d);
    assert!(matches!(
        &out_0d.verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { condition, .. })
            if condition == "reading_comparison_base_commutes"
    ));

    // 2. Collision-free naming when user scheme already names `fine_fiber_0` and `cand_fiber_0`.
    let fam_col = FamilySpec {
        name: "rf5_col".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u".into(),
            u_vars: vec!["u".into(), "t".into()],
            b_vars: vec!["b".into()],
            reading_q: vec![PolyExpr::param("u")],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![NamedPoly::new("fine_fiber_0", q_expr(0))],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: src("orig-u", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "c".into(),
            c_vars: vec!["c".into()],
            pi: vec![PolyExpr::param("c")],
            space: CandidateSpace::PolynomialScheme {
                equations: vec![NamedPoly::new("cand_fiber_0", q_expr(0))],
                invertibles: vec![],
                origin: src("orig-c", OriginKind::HumanAdopted),
            },
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new(
                "ok",
                PolyExpr::diff(PolyExpr::param("u"), PolyExpr::param("c")),
            )],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: Some(ReadingComparisonSpec {
            name: "rc_col".into(),
            fine_b_vars: vec!["bf1".into(), "bf2".into()],
            fine_q: vec![PolyExpr::param("u"), PolyExpr::param("t")],
            coarsen_r: vec![PolyExpr::param("bf1")],
            provenance: prov("orig-rc", MathClause::G142G4),
        }),
        provenance: prov("orig-fam", MathClause::G142G4),
    };
    let t_col = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "rf5_col_task".into(),
        family: fam_col,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![q_lit(1)],
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: Some(vec![q_lit(1), q_lit(2)]),
        provenance: prov("orig-task", MathClause::G142G4),
    })
    .unwrap();
    let out_col = solve_robustness_task(&t_col);
    assert_eq!(out_col.verdict, Verdict::Established);
    let rc_col = out_col
        .robustness
        .as_ref()
        .unwrap()
        .reading_comparison
        .as_ref()
        .unwrap();
    assert!(rc_col.fine_robust);
}

#[test]
fn rf6_chevalley_existential_never_emits_pass_without_restored_completion() {
    // u * (u^2 - 2) = 0: u = +-sqrt(2) passes via w = u, u = 0 fails.
    // Because u_pass has only irrational points, pass_witness cannot be verified with restoration.
    let fam = FamilySpec {
        name: "rf6_irrat_exist".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u".into(),
            u_vars: vec!["u".into()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![NamedPoly::new(
                    "u_branches",
                    PolyExpr::prod(
                        PolyExpr::param("u"),
                        PolyExpr::diff(PolyExpr::pow(PolyExpr::param("u"), 2), q_expr(2)),
                    ),
                )],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: src("orig-u", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "c".into(),
            c_vars: vec!["c".into()],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".into(),
                assignments: BTreeMap::from([("c".into(), CoordValue::Observed(q_lit(0)))]),
                origin: src("orig-c0", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Existential {
            witness_vars: vec!["w".into()],
            equations: vec![
                NamedPoly::new(
                    "w_irrat",
                    PolyExpr::diff(PolyExpr::pow(PolyExpr::param("w"), 2), q_expr(2)),
                ),
                NamedPoly::new(
                    "match_u",
                    PolyExpr::diff(PolyExpr::param("u"), PolyExpr::param("w")),
                ),
            ],
            invertibles: vec![],
            preservation: None,
        },
        reading_comparison: None,
        provenance: prov("orig-fam", MathClause::G142G7),
    };
    let task = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "rf6_task".into(),
        family: fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: None,
        designated_candidate: Some(CandidateSelector::ById("c0".into())),
        rational_fiber_probes: vec![],
        check_global_regular_section: false,
        check_universal_ring: false,
        provenance: prov("orig-chev", MathClause::G142G7),
    })
    .unwrap();
    let out = solve_chevalley_task(&task);
    assert_eq!(out.verdict, Verdict::Refuted);
    let chev = out.chevalley.as_ref().unwrap();
    assert!(!chev.mixed.is_empty);
    if let Some(mwp) = &chev.mixed_witness_pair {
        assert!(
            mwp.pass_witness.restored_completion.is_some(),
            "Existential pass_witness must never be emitted without restored_completion"
        );
    }
}

#[test]
fn rf7_raw_sequence_rejects_contradicting_observed_start_state() {
    let orig = src("orig-obs", OriginKind::RuntimeObservation);
    let pres = Presentation {
        name: "Rf7Pres".into(),
        coeff_domain: CoeffDomain::Q,
        sorts: vec![SortDecl {
            name: "S".into(),
            rank: 1,
            coeff_domain: CoeffDomain::Q,
            provenance: Some(orig.clone()),
        }],
        phases: vec![PhaseDecl {
            name: "P0".into(),
            coords: vec![
                CoordDecl::symbolic("x", "S"),
                CoordDecl::observed("k", "S", q_lit(5)),
            ],
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "step".into(),
            source_phase: "P0".into(),
            target_phase: "P0".into(),
            args: vec![],
            domain_laws: vec![],
            updates: BTreeMap::from([
                ("x".into(), PolyExpr::state("x")),
                ("k".into(), PolyExpr::state("k")),
            ]),
            provenance: None,
        }],
        observations: vec![ObservationDecl {
            name: "read".into(),
            phase: "P0".into(),
            components: vec![PolyExpr::state("k")],
            provenance: None,
        }],
        provenance: prov("orig-pres", MathClause::G140P7),
    };
    let fam = FamilySpec {
        name: "rf7_override_obs".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "r".into(),
            u_vars: vec!["u".into()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::FiniteMembers(vec![RealizationMember {
                id: "u0".into(),
                assignments: BTreeMap::from([("u".into(), CoordValue::Observed(q_lit(1)))]),
                is_raw_candidate: true,
                presentation: Some(pres),
                origin: orig,
            }]),
        },
        candidates: CandidateFamilySpec {
            name: "c".into(),
            c_vars: vec![],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".into(),
                assignments: BTreeMap::new(),
                origin: src("orig-c0", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![],
            invertibles: vec![],
            preservation: None,
            raw_sequence: Some(RawSequenceCheck {
                start_phase: "P0".into(),
                start_state: BTreeMap::from([("x".into(), q_lit(1)), ("k".into(), q_lit(9))]),
                steps: vec![("step".into(), vec![])],
                observation_name: "read".into(),
                baseline_step_index: None,
                provenance: prov("orig-seq", MathClause::G140P7),
            }),
        },
        reading_comparison: None,
        provenance: prov("orig-fam", MathClause::G140P7),
    };
    assert!(CheckedFamilySpec::validate(fam).is_err());
}
