//! PR #6437 Rerun4 非中心指摘（F1–F4 直接対応）の回帰テスト。

use super::*;
use crate::ir::change::{NamedPoly, PointDomain};
use crate::ir::family::{
    CandidateFamilySpec, CandidateMember, CandidateSpace, FamilySpec, GoodnessSpec,
    ReadingComparisonSpec, RealizationFamilySpec, RealizationMember, RealizationSpace,
};
use crate::ir::observation::{
    CandidateObservationDecl, CheckedObservationTask, ObservationTaskSpec,
};
use crate::ir::presentation::CoordValue;
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::Verdict;
use crate::ir::robustness::{
    CheckedChevalleyTask, CheckedRobustnessTask, ChevalleyTaskSpec, RobustnessTaskSpec,
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

fn z_expr(n: i64) -> PolyExpr {
    PolyExpr::constant(ScalarLit::int(n))
}

#[test]
fn rerun4_f1_reading_comparison_picks_fine_winner_for_coarse_counterexample() {
    let fam = FamilySpec {
        name: "r4_f1".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u".into(),
            u_vars: vec!["u".into()],
            b_vars: vec!["b".into()],
            reading_q: vec![q_expr(0)],
            space: RealizationSpace::FiniteMembers(vec![
                RealizationMember {
                    id: "u_fine".into(),
                    assignments: BTreeMap::from([("u".into(), CoordValue::Observed(q_lit(1)))]),
                    is_raw_candidate: false,
                    presentation: None,
                    origin: src("orig-u-fine", OriginKind::StaticAnalysis),
                },
                RealizationMember {
                    id: "u_coarse_only".into(),
                    assignments: BTreeMap::from([("u".into(), CoordValue::Observed(q_lit(2)))]),
                    is_raw_candidate: false,
                    presentation: None,
                    origin: src("orig-u-coarse", OriginKind::RuntimeObservation),
                },
            ]),
        },
        candidates: CandidateFamilySpec {
            name: "c".into(),
            c_vars: vec!["c".into()],
            pi: vec![q_expr(0)],
            space: CandidateSpace::FiniteMembers(vec![
                CandidateMember {
                    id: "c0_always_fail".into(),
                    assignments: BTreeMap::from([("c".into(), CoordValue::Observed(q_lit(0)))]),
                    origin: src("orig-c0", OriginKind::LlmCandidate),
                },
                CandidateMember {
                    id: "c1_fine_win".into(),
                    assignments: BTreeMap::from([("c".into(), CoordValue::Observed(q_lit(1)))]),
                    origin: src("orig-c1", OriginKind::HumanAdopted),
                },
            ]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new(
                "match",
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
    let task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "r4_f1_task".into(),
        family: fam,
        point_domain: PointDomain::RationalPoints,
        base_value: vec![q_lit(0)],
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: Some(vec![q_lit(1)]),
        provenance: prov("orig-t", MathClause::G142G4),
    })
    .unwrap();
    let rc = solve_robustness_task(&task)
        .robustness
        .unwrap()
        .reading_comparison
        .unwrap();
    assert!(!rc.coarse_robust);
    assert!(rc.fine_robust);
    let ce = rc.fine_only_counterexample.unwrap();
    assert_eq!(ce.realization.member_id.as_deref(), Some("u_coarse_only"));
    assert_eq!(ce.candidate_id.as_deref(), Some("c1_fine_win"));
}

#[test]
fn rerun4_f2_preserves_finite_candidate_meta_in_zero_dim_robustness_and_chevalley() {
    let c0_orig = src("orig-c0-mem", OriginKind::LlmCandidate);
    let fam_0d = FamilySpec {
        name: "r4_f2_0d".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u".into(),
            u_vars: vec!["u".into()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![NamedPoly::new(
                    "u_roots",
                    PolyExpr::prod(
                        PolyExpr::param("u"),
                        PolyExpr::diff(PolyExpr::param("u"), q_expr(1)),
                    ),
                )],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: src("orig-u-scheme", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "c".into(),
            c_vars: vec![],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c_zero_dim".into(),
                assignments: BTreeMap::new(),
                origin: c0_orig.clone(),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new("taut", q_expr(0))],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: prov("orig-fam", MathClause::G142G1),
    };
    let rob_0d = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "r4_f2_0d_task".into(),
        family: fam_0d,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: None,
        provenance: prov("orig-rob", MathClause::G142G1),
    })
    .unwrap();
    let out_0d = solve_robustness_task(&rob_0d);
    assert_eq!(out_0d.verdict, Verdict::Established);
    let cm_0d = out_0d.robustness.unwrap().common_candidate.unwrap();
    assert!(cm_0d.satisfied);
    assert_eq!(cm_0d.candidate_id.as_deref(), Some("c_zero_dim"));
    assert!(out_0d.provenance.origins.contains(&c0_orig));

    // CoeffDomain::Z mixed witness selects second FiniteMember ("c1_mix") with its id preserved.
    let u = PolyExpr::param("u");
    let c = PolyExpr::param("c");
    let mixed_z_fam = FamilySpec {
        name: "r4_f2_mixed_z".into(),
        coeff_domain: CoeffDomain::Z,
        realizations: RealizationFamilySpec {
            name: "u".into(),
            u_vars: vec!["u".into()],
            b_vars: vec!["b".into()],
            reading_q: vec![z_expr(0)],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![NamedPoly::new(
                    "u_pair",
                    PolyExpr::prod(u.clone(), PolyExpr::diff(u.clone(), z_expr(1))),
                )],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: src("orig-u-z", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "c".into(),
            c_vars: vec!["c".into()],
            pi: vec![z_expr(0)],
            space: CandidateSpace::FiniteMembers(vec![
                CandidateMember {
                    id: "c0_bad".into(),
                    assignments: BTreeMap::from([(
                        "c".into(),
                        CoordValue::Observed(ScalarLit::int(0)),
                    )]),
                    origin: src("orig-c0-z", OriginKind::LlmCandidate),
                },
                CandidateMember {
                    id: "c1_mix".into(),
                    assignments: BTreeMap::from([(
                        "c".into(),
                        CoordValue::Observed(ScalarLit::int(1)),
                    )]),
                    origin: src("orig-c1-z", OriginKind::HumanAdopted),
                },
            ]),
        },
        goodness: GoodnessSpec::Direct {
            // c=0 => 1 = 0 (always fail); c=1 => u - 1 = 0 (mixed on u in {0, 1}).
            equations: vec![NamedPoly::new(
                "mix_eq",
                PolyExpr::sum(
                    PolyExpr::prod(c.clone(), PolyExpr::diff(u, z_expr(1))),
                    PolyExpr::diff(z_expr(1), c),
                ),
            )],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: prov("orig-fam-z", MathClause::G142G3),
    };
    let chev_z = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "r4_f2_chev_z".into(),
        family: mixed_z_fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: None,
        designated_candidate: None,
        rational_fiber_probes: vec![],
        check_global_regular_section: false,
        check_universal_ring: false,
        provenance: prov("orig-chev-z", MathClause::G142G3),
    })
    .unwrap();
    let out_z = solve_chevalley_task(&chev_z);
    let mw = out_z
        .chevalley
        .as_ref()
        .and_then(|d| d.mixed_witness_pair.as_ref())
        .expect("mixed witness pair present");
    assert_eq!(mw.pass_witness.candidate_id.as_deref(), Some("c1_mix"));
    assert_eq!(mw.fail_witness.candidate_id.as_deref(), Some("c1_mix"));

    // Universal ring check with singleton FiniteMembers and designated_candidate == None.
    let univ_fam = FamilySpec {
        name: "r4_f2_univ_singleton".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u".into(),
            u_vars: vec!["u".into()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![NamedPoly::new(
                    "u_sq",
                    PolyExpr::pow(PolyExpr::param("u"), 2),
                )],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: src("orig-u-sq", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "c".into(),
            c_vars: vec!["c".into()],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c_univ_singleton".into(),
                assignments: BTreeMap::from([("c".into(), CoordValue::Observed(q_lit(1)))]),
                origin: src("orig-c-univ", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new(
                "nilpotent_u",
                PolyExpr::sum(
                    PolyExpr::param("u"),
                    PolyExpr::diff(PolyExpr::param("c"), q_expr(1)),
                ),
            )],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: prov("orig-fam-univ", MathClause::G142G2),
    };
    let chev_univ = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "r4_f2_chev_univ".into(),
        family: univ_fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: None,
        designated_candidate: None,
        rational_fiber_probes: vec![],
        check_global_regular_section: false,
        check_universal_ring: true,
        provenance: prov("orig-chev-univ", MathClause::G142G2),
    })
    .unwrap();
    let out_univ = solve_chevalley_task(&chev_univ);
    let uc = out_univ
        .chevalley
        .as_ref()
        .and_then(|d| d.universal_ring_contrast.as_ref())
        .expect("universal ring contrast evaluated");
    assert!(uc.evaluated);
    assert_eq!(uc.stable, Some(false));
}

#[test]
fn rerun4_f3_irrational_open_stratum_geom_point_preserves_invertibles() {
    let u = PolyExpr::param("u");
    let v = PolyExpr::param("v");
    let c = PolyExpr::param("c");
    let fam = FamilySpec {
        name: "r4_f3_geom_open".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u".into(),
            u_vars: vec!["u".into(), "v".into()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![
                    NamedPoly::new(
                        "irr_u",
                        PolyExpr::diff(PolyExpr::pow(u.clone(), 2), q_expr(2)),
                    ),
                    NamedPoly::new(
                        "split_v",
                        PolyExpr::prod(v.clone(), PolyExpr::diff(v.clone(), q_expr(1))),
                    ),
                ],
                invertibles: vec![NamedPoly::new("u_ne_1", PolyExpr::diff(u, q_expr(1)))],
                is_raw_candidate: false,
                origin: src("orig-u-irr", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "c".into(),
            c_vars: vec!["c".into()],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c_zero".into(),
                assignments: BTreeMap::from([("c".into(), CoordValue::Observed(q_lit(0)))]),
                origin: src("orig-c0", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new("match_v", PolyExpr::diff(v, c))],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: prov("orig-fam-f3", MathClause::G141D6),
    };
    let task = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "r4_f3_task".into(),
        family: fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: None,
        designated_candidate: None,
        rational_fiber_probes: vec![],
        check_global_regular_section: false,
        check_universal_ring: false,
        provenance: prov("orig-chev-f3", MathClause::G141D6),
    })
    .unwrap();
    let out = solve_chevalley_task(&task);
    let mw = out
        .chevalley
        .as_ref()
        .and_then(|d| d.mixed_witness_pair.as_ref())
        .expect("mixed witness pair present on irrational open stratum");
    let has_geom_open = |vals: &BTreeMap<String, String>| {
        vals.values()
            .any(|v| v.starts_with("geom_point(") && v.contains("!= 0"))
    };
    assert!(
        has_geom_open(&mw.pass_witness.realization.assignments),
        "expected geom_point with invertible != 0 on pass witness, got {:?}",
        mw.pass_witness.realization.assignments
    );
    assert!(
        has_geom_open(&mw.fail_witness.realization.assignments),
        "expected geom_point with invertible != 0 on fail witness, got {:?}",
        mw.fail_witness.realization.assignments
    );
    assert!(
        mw.fail_witness.residuals.iter().any(|r| r.contains("!= 0")),
        "expected fail residuals to retain != 0 invertible condition, got {:?}",
        mw.fail_witness.residuals
    );
}

#[test]
fn rerun4_f4_observation_provenance_includes_scheme_and_candidate_origins() {
    let u_scheme_orig = src("orig-u-scheme", OriginKind::StaticAnalysis);
    let c0_orig = src("orig-c0-mem", OriginKind::LlmCandidate);
    let fam_obs = FamilySpec {
        name: "r4_f4_obs".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u".into(),
            u_vars: vec!["u".into()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![NamedPoly::new(
                    "u_roots",
                    PolyExpr::prod(
                        PolyExpr::param("u"),
                        PolyExpr::diff(PolyExpr::param("u"), q_expr(1)),
                    ),
                )],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: u_scheme_orig.clone(),
            },
        },
        candidates: CandidateFamilySpec {
            name: "c".into(),
            c_vars: vec![],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c_zero_dim".into(),
                assignments: BTreeMap::new(),
                origin: c0_orig.clone(),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new("u_is_0", PolyExpr::param("u"))],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: prov("orig-fam", MathClause::G142G6),
    };
    let obs_task = CheckedObservationTask::validate(ObservationTaskSpec {
        name: "r4_f4_obs_task".into(),
        family: fam_obs,
        point_domain: PointDomain::RationalPoints,
        base_value: vec![],
        observations: vec![CandidateObservationDecl {
            id: "e_u".into(),
            components: vec![NamedPoly::new("u", PolyExpr::param("u"))],
            cost: None,
            origin: src("orig-e", OriginKind::HumanAdopted),
        }],
        law_readout: None,
        provenance: prov("orig-obs", MathClause::G142G6),
    })
    .unwrap();
    let obs_out = solve_observation_task(&obs_task);
    assert!(obs_out.provenance.origins.contains(&u_scheme_orig));
    assert!(obs_out.provenance.origins.contains(&c0_orig));
}
