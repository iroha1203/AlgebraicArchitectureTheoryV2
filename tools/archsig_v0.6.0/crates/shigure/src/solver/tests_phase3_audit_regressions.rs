use super::*;
use crate::ir::change::{NamedPoly, PointDomain};
use crate::ir::family::{
    CandidateFamilySpec, CandidateMember, CandidateSpace, CheckedFamilySpec, FamilySpec,
    GoodnessSpec, RawSequenceCheck, ReadingComparisonSpec, RealizationFamilySpec,
    RealizationMember, RealizationSpace,
};
use crate::ir::presentation::{
    CoordDecl, CoordValue, ObservationDecl, OperationDecl, PhaseDecl, Presentation, SortDecl,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::robustness::{
    CandidateSelector, CheckedChevalleyTask, CheckedRobustnessTask, ChevalleyTaskSpec,
    RobustnessTaskSpec,
};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::ir::validate::ValidationError;
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
fn f1_chevalley_base_none_preserves_reading_fiber_in_universal_ring() {
    let make_fam = |cand_space: CandidateSpace| FamilySpec {
        name: "f1_fiber_universal".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u_line".into(),
            u_vars: vec!["u".into()],
            b_vars: vec!["b".into()],
            reading_q: vec![PolyExpr::param("u")],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: src("orig-u", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "c_space".into(),
            c_vars: vec!["c".into()],
            pi: vec![PolyExpr::param("c")],
            space: cand_space,
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new(
                "ok_fiber",
                PolyExpr::diff(PolyExpr::param("u"), PolyExpr::param("c")),
            )],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: prov("orig-fam", MathClause::G140E5),
    };

    // Case A: Candidate PolynomialScheme + designated_candidate: Some(c = 1) + base_value: None
    let task_a = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "f1_scheme_designated".into(),
        family: make_fam(CandidateSpace::PolynomialScheme {
            equations: vec![],
            invertibles: vec![],
            origin: src("orig-c", OriginKind::HumanAdopted),
        }),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: None,
        designated_candidate: Some(CandidateSelector::ByValues(BTreeMap::from([(
            "c".into(),
            q_lit(1),
        )]))),
        rational_fiber_probes: vec![],
        check_global_regular_section: false,
        check_universal_ring: true,
        provenance: prov("orig-chev-a", MathClause::G140E5),
    })
    .expect("task_a validates");
    let out_a = solve_chevalley_task(&task_a);
    let ur_a = out_a
        .chevalley
        .as_ref()
        .and_then(|c| c.universal_ring_contrast.as_ref())
        .expect("universal_ring_contrast present");
    assert!(ur_a.evaluated);
    assert_eq!(ur_a.stable, Some(true));
    assert_eq!(ur_a.inhabited_stable, Some(true));

    // Case B: FiniteMembers candidate + designated_candidate: None + base_value: None
    let task_b = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "f1_finite_auto".into(),
        family: make_fam(CandidateSpace::FiniteMembers(vec![CandidateMember {
            id: "c1".into(),
            assignments: BTreeMap::from([("c".into(), CoordValue::Observed(q_lit(1)))]),
            origin: src("orig-c1", OriginKind::HumanAdopted),
        }])),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: None,
        designated_candidate: None,
        rational_fiber_probes: vec![],
        check_global_regular_section: false,
        check_universal_ring: true,
        provenance: prov("orig-chev-b", MathClause::G140E5),
    })
    .expect("task_b validates");
    let out_b = solve_chevalley_task(&task_b);
    let ur_b = out_b
        .chevalley
        .as_ref()
        .and_then(|c| c.universal_ring_contrast.as_ref())
        .expect("universal_ring_contrast present");
    assert!(ur_b.evaluated);
    assert_eq!(ur_b.stable, Some(true));
    assert_eq!(ur_b.inhabited_stable, Some(true));
}

#[test]
fn f2_integer_points_existential_inconsistent_affine_refutes_not_silences() {
    let fam = FamilySpec {
        name: "f2_z_inconsistent".into(),
        coeff_domain: CoeffDomain::Z,
        realizations: RealizationFamilySpec {
            name: "u_single".into(),
            u_vars: vec!["u".into()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::FiniteMembers(vec![RealizationMember {
                id: "u0".into(),
                assignments: BTreeMap::from([(
                    "u".into(),
                    CoordValue::Observed(ScalarLit::int(0)),
                )]),
                is_raw_candidate: false,
                presentation: None,
                origin: src("orig-u0", OriginKind::StaticAnalysis),
            }]),
        },
        candidates: CandidateFamilySpec {
            name: "c_single".into(),
            c_vars: vec!["c".into()],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".into(),
                assignments: BTreeMap::from([(
                    "c".into(),
                    CoordValue::Observed(ScalarLit::int(0)),
                )]),
                origin: src("orig-c0", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Existential {
            witness_vars: vec!["w".into()],
            equations: vec![NamedPoly::new(
                "two_w_minus_1",
                PolyExpr::diff(
                    PolyExpr::prod(PolyExpr::int(2), PolyExpr::param("w")),
                    PolyExpr::int(1),
                ),
            )],
            invertibles: vec![],
            preservation: None,
        },
        reading_comparison: None,
        provenance: prov("orig-fam", MathClause::G141D4),
    };

    let task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "f2_task".into(),
        family: fam,
        point_domain: PointDomain::IntegerPoints,
        base_value: vec![],
        designated_candidate: Some(CandidateSelector::ById("c0".into())),
        check_universal_ring: false,
        fine_base_value: None,
        provenance: prov("orig-task", MathClause::G141D4),
    })
    .expect("task validates");

    let out = solve_robustness_task(&task);
    assert_eq!(out.verdict, Verdict::Refuted);
    let vd = out
        .robustness
        .as_ref()
        .and_then(|r| r.valid_designated.as_ref())
        .expect("valid_designated present");
    assert!(!vd.satisfied);
    assert!(vd.counterexample.is_some());
}

#[test]
fn f3_positive_dim_polynomial_scheme_witness_respects_invertibles() {
    // 1. G_m: u != 0 -> sample witness must NOT be "0".
    let gm_fam = FamilySpec {
        name: "f3_gm".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u_gm".into(),
            u_vars: vec!["u".into()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![],
                invertibles: vec![NamedPoly::new("u_nz", PolyExpr::param("u"))],
                is_raw_candidate: false,
                origin: src("orig-gm", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "c_single".into(),
            c_vars: vec!["c".into()],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".into(),
                assignments: BTreeMap::from([("c".into(), CoordValue::Observed(q_lit(1)))]),
                origin: src("orig-c0", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new("trivial", q_expr(0))],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: prov("orig-fam", MathClause::G142G2),
    };
    let t_gm = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "f3_gm_task".into(),
        family: gm_fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        designated_candidate: Some(CandidateSelector::ById("c0".into())),
        check_universal_ring: false,
        fine_base_value: None,
        provenance: prov("orig-task", MathClause::G142G2),
    })
    .expect("gm task validates");
    let out_gm = solve_robustness_task(&t_gm);
    let fne_gm = &out_gm.robustness.as_ref().unwrap().fiber_non_empty;
    assert!(fne_gm.non_empty);
    let u_val = fne_gm
        .witness
        .as_ref()
        .and_then(|w| w.assignments.get("u"))
        .expect("gm witness has u");
    assert_ne!(u_val, "0", "G_m fiber witness must satisfy u != 0");

    // 2. Coupled 2D diagonal u1 - u2 = 0 with u1 != 0: witness must satisfy u1 == u2 and u1 != 0.
    let coupled_fam = FamilySpec {
        name: "f3_coupled".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u_diag".into(),
            u_vars: vec!["u1".into(), "u2".into()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![NamedPoly::new(
                    "diag",
                    PolyExpr::diff(PolyExpr::param("u1"), PolyExpr::param("u2")),
                )],
                invertibles: vec![NamedPoly::new("u1_nz", PolyExpr::param("u1"))],
                is_raw_candidate: false,
                origin: src("orig-diag", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "c_single".into(),
            c_vars: vec!["c".into()],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".into(),
                assignments: BTreeMap::from([("c".into(), CoordValue::Observed(q_lit(1)))]),
                origin: src("orig-c0", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new("trivial", q_expr(0))],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: prov("orig-fam", MathClause::G142G2),
    };
    let t_cp = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "f3_coupled_task".into(),
        family: coupled_fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        designated_candidate: Some(CandidateSelector::ById("c0".into())),
        check_universal_ring: false,
        fine_base_value: None,
        provenance: prov("orig-task", MathClause::G142G2),
    })
    .expect("coupled task validates");
    let out_cp = solve_robustness_task(&t_cp);
    let fne_cp = &out_cp.robustness.as_ref().unwrap().fiber_non_empty;
    assert!(fne_cp.non_empty);
    let assign = &fne_cp
        .witness
        .as_ref()
        .expect("coupled witness")
        .assignments;
    assert_ne!(assign.get("u1").map(String::as_str), Some("0"));
    assert_eq!(assign.get("u1"), assign.get("u2"));
}

#[test]
fn f4_empty_fiber_reading_coarse_robust_and_mixed_finite_u_scheme_c() {
    // Part 4a: Empty U_b with designated vs empty C_b -> coarse_robust matches quantifiers.
    let make_empty_rc_fam = |cand_space: CandidateSpace| FamilySpec {
        name: "f4a_empty_u".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u_empty".into(),
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
            name: "c_space".into(),
            c_vars: vec!["c".into()],
            pi: vec![PolyExpr::param("c")],
            space: cand_space,
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new("trivial", q_expr(0))],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: Some(ReadingComparisonSpec {
            name: "rc".into(),
            fine_b_vars: vec!["bf".into()],
            fine_q: vec![PolyExpr::param("u")],
            coarsen_r: vec![q_expr(0)],
            provenance: prov("orig-rc", MathClause::G140E5Dot1),
        }),
        provenance: prov("orig-fam", MathClause::G140E5Dot1),
    };

    // At b = 1, reading_q = 0 leaves U_1 = empty while pi(c0 = 1) = 1 matches C_1!
    let t_4a_des = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "f4a_des".into(),
        family: make_empty_rc_fam(CandidateSpace::FiniteMembers(vec![CandidateMember {
            id: "c0".into(),
            assignments: BTreeMap::from([("c".into(), CoordValue::Observed(q_lit(1)))]),
            origin: src("orig-c0", OriginKind::HumanAdopted),
        }])),
        point_domain: PointDomain::RationalPoints,
        base_value: vec![q_lit(1)],
        designated_candidate: Some(CandidateSelector::ById("c0".into())),
        check_universal_ring: false,
        fine_base_value: None,
        provenance: prov("orig-task", MathClause::G140E5Dot1),
    })
    .expect("f4a_des validates");
    let out_4a_des = solve_robustness_task(&t_4a_des);
    assert_eq!(out_4a_des.verdict, Verdict::Refuted);
    let det_4a_des = out_4a_des.robustness.as_ref().unwrap();
    assert!(!det_4a_des.fiber_non_empty.non_empty);
    assert!(det_4a_des.valid_designated.as_ref().unwrap().satisfied);
    assert!(
        det_4a_des
            .reading_comparison
            .as_ref()
            .unwrap()
            .coarse_robust
    );

    let t_4a_empty_c = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "f4a_empty_c".into(),
        family: make_empty_rc_fam(CandidateSpace::FiniteMembers(vec![])),
        point_domain: PointDomain::RationalPoints,
        base_value: vec![q_lit(1)],
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: None,
        provenance: prov("orig-task", MathClause::G140E5Dot1),
    })
    .expect("f4a_empty_c validates");
    let out_4a_empty_c = solve_robustness_task(&t_4a_empty_c);
    assert_eq!(out_4a_empty_c.verdict, Verdict::Refuted);
    let det_4a_empty_c = out_4a_empty_c.robustness.as_ref().unwrap();
    assert!(!det_4a_empty_c.common_candidate.as_ref().unwrap().satisfied);
    assert!(
        !det_4a_empty_c
            .reading_comparison
            .as_ref()
            .unwrap()
            .coarse_robust
    );

    // Part 4b: Mixed (FiniteMembers U, NonFiniteScheme C = A^1_c) over AlgebraicClosure
    // with fine_base_value yielding both empty fine fiber and non-empty fine fiber.
    let mixed_fam = FamilySpec {
        name: "f4b_mixed".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u_two".into(),
            u_vars: vec!["u".into()],
            b_vars: vec!["b".into()],
            reading_q: vec![q_expr(0)],
            space: RealizationSpace::FiniteMembers(vec![
                RealizationMember {
                    id: "u0".into(),
                    assignments: BTreeMap::from([("u".into(), CoordValue::Observed(q_lit(0)))]),
                    is_raw_candidate: false,
                    presentation: None,
                    origin: src("orig-u0", OriginKind::StaticAnalysis),
                },
                RealizationMember {
                    id: "u1".into(),
                    assignments: BTreeMap::from([("u".into(), CoordValue::Observed(q_lit(1)))]),
                    is_raw_candidate: false,
                    presentation: None,
                    origin: src("orig-u1", OriginKind::RuntimeObservation),
                },
            ]),
        },
        candidates: CandidateFamilySpec {
            name: "c_line".into(),
            c_vars: vec!["c".into()],
            pi: vec![q_expr(0)],
            space: CandidateSpace::PolynomialScheme {
                equations: vec![],
                invertibles: vec![],
                origin: src("orig-c-line", OriginKind::HumanAdopted),
            },
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new(
                "ok_match",
                PolyExpr::diff(PolyExpr::param("u"), PolyExpr::param("c")),
            )],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: Some(ReadingComparisonSpec {
            name: "rc_split".into(),
            fine_b_vars: vec!["bf".into()],
            fine_q: vec![PolyExpr::param("u")],
            coarsen_r: vec![q_expr(0)],
            provenance: prov("orig-rc", MathClause::G142G4),
        }),
        provenance: prov("orig-fam", MathClause::G142G4),
    };

    // Empty fine fiber bf = 2 while C is NonFiniteScheme A^1_c -> fine_robust == true
    let t_4b_empty_fine = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "f4b_empty_fine".into(),
        family: mixed_fam.clone(),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![q_lit(0)],
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: Some(vec![q_lit(2)]),
        provenance: prov("orig-task", MathClause::G142G4),
    })
    .expect("t_4b_empty_fine validates");
    let out_4b_empty_fine = solve_robustness_task(&t_4b_empty_fine);
    assert_eq!(out_4b_empty_fine.verdict, Verdict::Refuted);
    let rc_empty = out_4b_empty_fine
        .robustness
        .as_ref()
        .unwrap()
        .reading_comparison
        .as_ref()
        .unwrap();
    assert!(!rc_empty.coarse_robust);
    assert!(rc_empty.fine_robust);
    assert!(rc_empty.coarse_implies_fine_preserved);

    // Non-empty fine fiber bf = 1 selects u = 1 only -> c = 1 makes fine_robust == true
    let t_4b_nonempty_fine = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "f4b_nonempty_fine".into(),
        family: mixed_fam.clone(),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![q_lit(0)],
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: Some(vec![q_lit(1)]),
        provenance: prov("orig-task", MathClause::G142G4),
    })
    .expect("t_4b_nonempty_fine validates");
    let out_4b_nonempty_fine = solve_robustness_task(&t_4b_nonempty_fine);
    assert_eq!(out_4b_nonempty_fine.verdict, Verdict::Refuted);
    let rc_nonempty = out_4b_nonempty_fine
        .robustness
        .as_ref()
        .unwrap()
        .reading_comparison
        .as_ref()
        .unwrap();
    assert!(!rc_nonempty.coarse_robust);
    assert!(rc_nonempty.fine_robust);
    assert!(rc_nonempty.coarse_implies_fine_preserved);

    // With designated c = 1 on the same fine fiber, coarse counterexample u = 0 is recorded
    let t_4b_des = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "f4b_nonempty_fine_des".into(),
        family: mixed_fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![q_lit(0)],
        designated_candidate: Some(CandidateSelector::ByValues(BTreeMap::from([(
            "c".into(),
            q_lit(1),
        )]))),
        check_universal_ring: false,
        fine_base_value: Some(vec![q_lit(1)]),
        provenance: prov("orig-task", MathClause::G142G4),
    })
    .expect("t_4b_des validates");
    let rc_des = solve_robustness_task(&t_4b_des)
        .robustness
        .unwrap()
        .reading_comparison
        .unwrap();
    assert!(!rc_des.coarse_robust);
    assert!(rc_des.fine_robust);
    assert!(rc_des.coarse_implies_fine_preserved);
    assert!(rc_des.fine_only_counterexample.is_some());
}

#[test]
fn f5_empty_fiber_universal_ring_consistent_across_designated_and_none() {
    for designated in [Some(CandidateSelector::ById("c0".into())), None] {
        let fam = FamilySpec {
            name: "f5_empty_finite_q".into(),
            coeff_domain: CoeffDomain::Q,
            realizations: RealizationFamilySpec {
                name: "u_empty".into(),
                u_vars: vec!["u".into()],
                b_vars: vec!["b".into()],
                reading_q: vec![PolyExpr::param("u")],
                space: RealizationSpace::FiniteMembers(vec![RealizationMember {
                    id: "u1".into(),
                    assignments: BTreeMap::from([("u".into(), CoordValue::Observed(q_lit(1)))]),
                    is_raw_candidate: false,
                    presentation: None,
                    origin: src("orig-u1", OriginKind::StaticAnalysis),
                }]),
            },
            candidates: CandidateFamilySpec {
                name: "c_space".into(),
                c_vars: vec!["c".into()],
                pi: vec![PolyExpr::param("c")],
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
            reading_comparison: None,
            provenance: prov("orig-fam", MathClause::G140E5),
        };
        let task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
            name: "f5_task".into(),
            family: fam,
            point_domain: PointDomain::RationalPoints,
            base_value: vec![q_lit(0)], // fiber U_0 = empty while C_0 = {c0}
            designated_candidate: designated,
            check_universal_ring: true,
            fine_base_value: None,
            provenance: prov("orig-task", MathClause::G140E5),
        })
        .expect("task validates");
        let out = solve_robustness_task(&task);
        assert!(
            matches!(
                out.verdict,
                Verdict::Undetermined(SilenceReason::UniversalRingOutOfScope { .. })
            ),
            "expected UniversalRingOutOfScope consistently, got {:?}",
            out.verdict
        );
    }
}

#[test]
fn f6_raw_sequence_rejects_observation_arity_mismatch_across_phases() {
    let orig = src("orig-p7", OriginKind::RuntimeObservation);
    let pres = Presentation {
        name: "RawArityPres".into(),
        coeff_domain: CoeffDomain::Q,
        sorts: vec![SortDecl {
            name: "S".into(),
            rank: 1,
            coeff_domain: CoeffDomain::Q,
            provenance: Some(orig.clone()),
        }],
        phases: vec![
            PhaseDecl {
                name: "P0".into(),
                coords: vec![CoordDecl::symbolic("x", "S")],
                state_laws: vec![],
                provenance: None,
            },
            PhaseDecl {
                name: "P1".into(),
                coords: vec![CoordDecl::symbolic("x", "S")],
                state_laws: vec![],
                provenance: None,
            },
        ],
        operations: vec![OperationDecl {
            name: "go".into(),
            source_phase: "P0".into(),
            target_phase: "P1".into(),
            args: vec![],
            domain_laws: vec![],
            updates: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
            provenance: None,
        }],
        observations: vec![
            ObservationDecl {
                name: "read".into(),
                phase: "P0".into(),
                components: vec![PolyExpr::state("x")],
                provenance: None,
            },
            ObservationDecl {
                name: "read".into(),
                phase: "P1".into(),
                components: vec![
                    PolyExpr::state("x"),
                    PolyExpr::sum(PolyExpr::state("x"), q_expr(1)),
                ],
                provenance: None,
            },
        ],
        provenance: prov("orig-pres", MathClause::G140P7),
    };

    let fam = FamilySpec {
        name: "f6_arity_mismatch".into(),
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
                origin: orig.clone(),
            }]),
        },
        candidates: CandidateFamilySpec {
            name: "c".into(),
            c_vars: vec!["c".into()],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".into(),
                assignments: BTreeMap::from([("c".into(), CoordValue::Observed(q_lit(1)))]),
                origin: src("orig-c0", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![],
            invertibles: vec![],
            preservation: None,
            raw_sequence: Some(RawSequenceCheck {
                start_phase: "P0".into(),
                start_state: BTreeMap::from([("x".into(), q_lit(1))]),
                steps: vec![("go".into(), vec![])],
                observation_name: "read".into(),
                baseline_step_index: None,
                provenance: prov("orig-seq", MathClause::G140P7),
            }),
        },
        reading_comparison: None,
        provenance: prov("orig-fam", MathClause::G140P7),
    };

    let err = CheckedFamilySpec::validate(fam).expect_err("arity mismatch must be rejected");
    assert!(matches!(err, ValidationError::ArityMismatch { .. }));
}

#[test]
fn f7_provenance_member_metadata_and_laurent_ring_labels() {
    let raw_origin = src("orig-u1-raw", OriginKind::LlmCandidate);
    let cand_origin = src("orig-c-scheme", OriginKind::HumanAdopted);
    let fam = FamilySpec {
        name: "f7_meta_fam".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u_mixed".into(),
            u_vars: vec!["u".into()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::FiniteMembers(vec![
                RealizationMember {
                    id: "u0".into(),
                    assignments: BTreeMap::from([("u".into(), CoordValue::Observed(q_lit(0)))]),
                    is_raw_candidate: false,
                    presentation: None,
                    origin: src("orig-u0", OriginKind::StaticAnalysis),
                },
                RealizationMember {
                    id: "u1_raw".into(),
                    assignments: BTreeMap::from([("u".into(), CoordValue::Observed(q_lit(1)))]),
                    is_raw_candidate: true,
                    presentation: None,
                    origin: raw_origin.clone(),
                },
            ]),
        },
        candidates: CandidateFamilySpec {
            name: "c_line".into(),
            c_vars: vec!["c".into()],
            pi: vec![],
            space: CandidateSpace::PolynomialScheme {
                equations: vec![],
                invertibles: vec![],
                origin: cand_origin.clone(),
            },
        },
        // Only u = 0 succeeds (with c = 0); u1_raw (u = 1) fails u = 0, so pointwise counterexample hits u1_raw.
        goodness: GoodnessSpec::Direct {
            equations: vec![
                NamedPoly::new("u_zero", PolyExpr::param("u")),
                NamedPoly::new("c_zero", PolyExpr::param("c")),
            ],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: prov("orig-fam", MathClause::G142G7),
    };

    // 1. Chevalley top-level provenance includes realization & candidate member origins.
    let chev_task = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "f7_chev".into(),
        family: fam.clone(),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: None,
        designated_candidate: None,
        rational_fiber_probes: vec![],
        check_global_regular_section: false,
        check_universal_ring: false,
        provenance: prov("orig-chev", MathClause::G142G7),
    })
    .expect("chev task validates");
    let chev_out = solve_chevalley_task(&chev_task);
    assert!(chev_out.provenance.origins.contains(&raw_origin));
    assert!(chev_out.provenance.origins.contains(&cand_origin));

    // 2. Mixed (FiniteMembers U, NonFiniteScheme C) symbolic pointwise counterexample preserves u1_raw metadata.
    let rob_task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "f7_rob".into(),
        family: fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: None,
        provenance: prov("orig-rob", MathClause::G142G1),
    })
    .expect("rob task validates");
    let rob_out = solve_robustness_task(&rob_task);
    assert_eq!(rob_out.verdict, Verdict::Refuted);
    let ce = rob_out
        .robustness
        .as_ref()
        .and_then(|r| r.pointwise.as_ref())
        .and_then(|pw| pw.counterexample.as_ref())
        .expect("pw counterexample at u1_raw");
    assert_eq!(ce.member_id.as_deref(), Some("u1_raw"));
    assert!(ce.is_raw_candidate);
    assert_eq!(ce.origin, raw_origin);

    // 3. Laurent ring label reflects actual invertibles (`k[t]` vs `k[t, t^(-1)]`).
    let mk_sec_task = |invs: Vec<NamedPoly>| {
        let fam_sec = FamilySpec {
            name: "f7_laurent".into(),
            coeff_domain: CoeffDomain::Q,
            realizations: RealizationFamilySpec {
                name: "base".into(),
                u_vars: vec!["t".into()],
                b_vars: vec![],
                reading_q: vec![],
                space: RealizationSpace::PolynomialScheme {
                    equations: vec![],
                    invertibles: invs,
                    is_raw_candidate: false,
                    origin: src("orig-t", OriginKind::StaticAnalysis),
                },
            },
            candidates: CandidateFamilySpec {
                name: "sec".into(),
                c_vars: vec!["z".into()],
                pi: vec![],
                space: CandidateSpace::PolynomialScheme {
                    equations: vec![],
                    invertibles: vec![],
                    origin: src("orig-z", OriginKind::HumanAdopted),
                },
            },
            goodness: GoodnessSpec::Direct {
                equations: vec![NamedPoly::new(
                    "sqrt_t",
                    PolyExpr::diff(PolyExpr::pow(PolyExpr::param("z"), 2), PolyExpr::param("t")),
                )],
                invertibles: vec![],
                preservation: None,
                raw_sequence: None,
            },
            reading_comparison: None,
            provenance: prov("orig-fam", MathClause::G141D7),
        };
        CheckedChevalleyTask::validate(ChevalleyTaskSpec {
            name: "f7_sec".into(),
            family: fam_sec,
            point_domain: PointDomain::AlgebraicClosure,
            base_value: None,
            designated_candidate: None,
            rational_fiber_probes: vec![],
            check_global_regular_section: true,
            check_universal_ring: false,
            provenance: prov("orig-sec", MathClause::G141D7),
        })
        .unwrap()
    };

    let det_a1 = solve_chevalley_task(&mk_sec_task(vec![]))
        .chevalley
        .unwrap()
        .global_regular_section
        .unwrap();
    assert_eq!(det_a1.exists, Some(false));
    let msg_a1 = det_a1.obstruction_detail.unwrap();
    assert!(msg_a1.contains("in k[t]:"), "got {msg_a1}");

    let det_gm = solve_chevalley_task(&mk_sec_task(vec![NamedPoly::new(
        "t_nz",
        PolyExpr::param("t"),
    )]))
    .chevalley
    .unwrap()
    .global_regular_section
    .unwrap();
    assert_eq!(det_gm.exists, Some(false));
    let msg_gm = det_gm.obstruction_detail.unwrap();
    assert!(msg_gm.contains("in k[t, t^(-1)]:"), "got {msg_gm}");
}
