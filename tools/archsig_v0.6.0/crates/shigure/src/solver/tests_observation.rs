//! `shigure_observations` ソルバの網羅単体テスト（AC5・AC6・G5–G6・W4・W6）。

use crate::ir::change::{NamedPoly, PointDomain};
use crate::ir::family::{
    CandidateFamilySpec, CandidateMember, CandidateSpace, FamilySpec, GoodnessSpec,
    RealizationFamilySpec, RealizationMember, RealizationSpace,
};
use crate::ir::observation::{
    CandidateObservationDecl, CheckedObservationTask, LawReadoutSpec, ObservationTaskSpec,
};
use crate::ir::presentation::CoordValue;
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::solver::solve_observation_task;
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet};

fn src(id: &str, kind: OriginKind) -> SourceRef {
    SourceRef::new(id, kind)
}

fn q(n: i64) -> ScalarLit {
    ScalarLit::rat(n, 1).expect("integer rational")
}

fn w4_obs_family() -> FamilySpec {
    let mem = |id: &str, a: i64, b: i64, c: i64| RealizationMember {
        id: id.to_owned(),
        assignments: BTreeMap::from([
            ("a".to_owned(), CoordValue::Observed(q(a))),
            ("b".to_owned(), CoordValue::Observed(q(b))),
            ("g".to_owned(), CoordValue::Observed(q(c))),
        ]),
        is_raw_candidate: false,
        presentation: None,
        origin: src(id, OriginKind::StaticAnalysis),
    };
    FamilySpec {
        name: "W4Obs".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["a".to_owned(), "b".to_owned(), "g".to_owned()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::FiniteMembers(vec![
                // For candidate c=0: goodness a == 0 holds on u_pass_* and fails on u_fail_*.
                mem("u_pass_0", 0, 0, 0),
                mem("u_pass_1", 0, 1, 0),
                mem("u_fail_0", 1, 0, 1),
                mem("u_fail_1", 1, 1, 1),
                // Note: e2 = b alone agrees on (u_pass_0, u_fail_0) and (u_pass_1, u_fail_1),
                // e3 = a + b separates pairs iff e2 or e3? Wait: let's engineer exact W4 {e1} and {e2, e3}!
            ]),
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec!["c".to_owned()],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".to_owned(),
                assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(0)))]),
                origin: src("c0", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new(
                "diag",
                PolyExpr::diff(PolyExpr::param("a"), PolyExpr::param("c")),
            )],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    }
}

#[test]
fn observation_w4_enumerates_all_minimal_sufficient_sets_and_cost_ranking() {
    // 4 pairs (u_pass_0/1 vs u_fail_0/1) with:
    //   e1 = a              (separates all 4 distinguishing pairs!)
    //   e2 = b              (separates (u_pass_0, u_fail_1) & (u_pass_1, u_fail_0), NOT (0,0) or (1,1))
    //   e3 = a + b          (at (u_pass_0=0+0=0, u_fail_0=1+0=1) and (u_pass_1=0+1=1, u_fail_1=1+1=2),
    //                        fails ONLY on (u_pass_1: 0+1=1, u_fail_0: 1+0=1)!)
    // Together, {e2, e3} separates (0,1) vs (1,0) via e2 AND (0,0) vs (1,0), (0,1) vs (1,1) via e3!
    // Hence ALL inclusion-minimal sufficient sets are EXACTLY {e1} and {e2, e3}!
    let obs = vec![
        CandidateObservationDecl {
            id: "e1".to_owned(),
            components: vec![NamedPoly::new("v", PolyExpr::param("a"))],
            cost: Some(BigInt::from(10)),
            origin: src("obs-e1", OriginKind::StaticAnalysis),
        },
        CandidateObservationDecl {
            id: "e2".to_owned(),
            components: vec![NamedPoly::new("v", PolyExpr::param("b"))],
            cost: Some(BigInt::from(2)),
            origin: src("obs-e2", OriginKind::RuntimeObservation),
        },
        CandidateObservationDecl {
            id: "e3".to_owned(),
            components: vec![NamedPoly::new(
                "v",
                PolyExpr::sum(PolyExpr::param("a"), PolyExpr::param("b")),
            )],
            cost: Some(BigInt::from(3)),
            origin: src("obs-e3", OriginKind::RuntimeObservation),
        },
    ];
    let task = CheckedObservationTask::validate(ObservationTaskSpec {
        name: "w4_minimal_obs".to_owned(),
        family: w4_obs_family(),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        observations: obs,
        law_readout: None,
        provenance: Provenance::new(vec![], vec![MathClause::G142G5, MathClause::G142G6]),
    })
    .unwrap();

    let out = solve_observation_task(&task);
    assert_eq!(out.verdict, Verdict::Established);
    let det = out.observations.expect("observation detail");
    assert!(det.sufficient);
    assert_eq!(det.distinguishing_pair_count, 4);
    assert!(det.insufficiency_witness.is_none());

    let found_sets: BTreeSet<Vec<String>> = det
        .minimal_sufficient_sets
        .iter()
        .map(|s| s.observations.clone())
        .collect();
    assert_eq!(
        found_sets,
        BTreeSet::from([
            vec!["e1".to_owned()],
            vec!["e2".to_owned(), "e3".to_owned()],
        ])
    );

    // Every minimal set must produce a single-removal counterexample per removed element!
    for min_set in &det.minimal_sufficient_sets {
        assert_eq!(
            min_set.removal_counterexamples.len(),
            min_set.observations.len(),
            "missing removal counterexample for {:?}",
            min_set.observations
        );
    }

    // Cost ranking preserves ALL minimal sets, ordering {e2, e3} (cost 5) ahead of {e1} (cost 10).
    assert_eq!(det.cost_ranked_sets.len(), 2);
    assert_eq!(det.cost_ranked_sets[0].rank, 1);
    assert_eq!(
        det.cost_ranked_sets[0].observations,
        vec!["e2".to_owned(), "e3".to_owned()]
    );
    assert_eq!(det.cost_ranked_sets[0].total_cost, "5");
    assert_eq!(det.cost_ranked_sets[1].rank, 2);
    assert_eq!(det.cost_ranked_sets[1].observations, vec!["e1".to_owned()]);
    assert_eq!(det.cost_ranked_sets[1].total_cost, "10");
}

#[test]
fn observation_insufficiency_and_zero_distinguishing_pair_boundaries() {
    // 1. Insufficient observation set -> Verdict::Refuted + InsufficiencyWitness
    let task_insuff = CheckedObservationTask::validate(ObservationTaskSpec {
        name: "insuff".to_owned(),
        family: w4_obs_family(),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        observations: vec![CandidateObservationDecl {
            id: "e2".to_owned(),
            components: vec![NamedPoly::new("v", PolyExpr::param("b"))],
            cost: None,
            origin: src("obs-e2", OriginKind::StaticAnalysis),
        }],
        law_readout: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    let out_insuff = solve_observation_task(&task_insuff);
    assert_eq!(out_insuff.verdict, Verdict::Refuted);
    let det_i = out_insuff.observations.unwrap();
    assert!(!det_i.sufficient);
    assert!(det_i.minimal_sufficient_sets.is_empty());
    let iw = det_i.insufficiency_witness.expect("insufficiency witness");
    assert!(iw.identical_observation_values.contains_key("e2"));

    // 2. Zero distinguishing pairs (all pairs uniformly pass goodness) -> minimal sufficient set = {{}}
    let mut uniform_fam = w4_obs_family();
    uniform_fam.goodness = GoodnessSpec::Direct {
        equations: vec![NamedPoly::new("zero", PolyExpr::rat(0, 1).unwrap())],
        invertibles: vec![],
        preservation: None,
        raw_sequence: None,
    };
    let task_empty_d = CheckedObservationTask::validate(ObservationTaskSpec {
        name: "empty_dist_pairs".to_owned(),
        family: uniform_fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        observations: vec![CandidateObservationDecl {
            id: "e1".to_owned(),
            components: vec![NamedPoly::new("v", PolyExpr::param("a"))],
            cost: None,
            origin: src("obs-e1", OriginKind::StaticAnalysis),
        }],
        law_readout: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    let out_ed = solve_observation_task(&task_empty_d);
    assert_eq!(out_ed.verdict, Verdict::Established);
    let det_ed = out_ed.observations.unwrap();
    assert!(det_ed.sufficient);
    assert_eq!(det_ed.distinguishing_pair_count, 0);
    assert_eq!(det_ed.minimal_sufficient_sets.len(), 1);
    assert!(det_ed.minimal_sufficient_sets[0].observations.is_empty());
}

#[test]
fn observation_w6_law_readout_adequacy_contrasts_with_decision_chi_e_inadequacy() {
    // W6: two realizations rho=0 (good) and rho=1 (bad) share the same coarse Law readout b = rho*(rho-1) = 0,
    // so coarse observation is adequate for `law_readout` ("0" == "0"), yet INADEQUATE for decision chi_E!
    // Candidate observation e_rho(u) = rho separates them cleanly.
    let rho = PolyExpr::param("rho");
    let fam = FamilySpec {
        name: "W6Obs".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["rho".to_owned()],
            b_vars: vec!["b".to_owned()],
            reading_q: vec![PolyExpr::prod(
                rho.clone(),
                PolyExpr::diff(rho.clone(), PolyExpr::rat(1, 1).unwrap()),
            )],
            space: RealizationSpace::FiniteMembers(vec![
                RealizationMember {
                    id: "rho_trivial".to_owned(),
                    assignments: BTreeMap::from([("rho".to_owned(), CoordValue::Observed(q(0)))]),
                    is_raw_candidate: false,
                    presentation: None,
                    origin: src("w6-r0", OriginKind::StaticAnalysis),
                },
                RealizationMember {
                    id: "rho_nontrivial".to_owned(),
                    assignments: BTreeMap::from([("rho".to_owned(), CoordValue::Observed(q(1)))]),
                    is_raw_candidate: false,
                    presentation: None,
                    origin: src("w6-r1", OriginKind::RuntimeObservation),
                },
            ]),
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
            equations: vec![NamedPoly::new("chi_e", rho.clone())],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };

    // With NO observations: coarse b alone is inadequate for decision (D = empty over {}, even though Law readout is constant 0).
    let task_coarse = CheckedObservationTask::validate(ObservationTaskSpec {
        name: "w6_coarse_only".to_owned(),
        family: fam.clone(),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![q(0)],
        observations: vec![],
        law_readout: Some(LawReadoutSpec {
            name: "coarse_law_readout".to_owned(),
            components: vec![NamedPoly::new(
                "law",
                PolyExpr::prod(
                    rho.clone(),
                    PolyExpr::diff(rho.clone(), PolyExpr::rat(1, 1).unwrap()),
                ),
            )],
            provenance: Provenance::default(),
        }),
        provenance: Provenance::default(),
    })
    .unwrap();
    let out_c = solve_observation_task(&task_coarse);
    assert_eq!(out_c.verdict, Verdict::Refuted);
    let det_c = out_c.observations.unwrap();
    let lrc = det_c
        .law_readout_comparison
        .expect("law readout comparison");
    assert!(lrc.coarse_adequate_for_law_readout);
    assert!(!lrc.coarse_adequate_for_decision);

    // Adding observation e_rho(u) = rho separates them -> sufficient & minimal set = {e_rho}
    let task_obs = CheckedObservationTask::validate(ObservationTaskSpec {
        name: "w6_with_e_rho".to_owned(),
        family: fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![q(0)],
        observations: vec![CandidateObservationDecl {
            id: "e_rho".to_owned(),
            components: vec![NamedPoly::new("rho_obs", rho.clone())],
            cost: None,
            origin: src("w6-obs", OriginKind::StaticAnalysis),
        }],
        law_readout: Some(LawReadoutSpec {
            name: "coarse_law_readout".to_owned(),
            components: vec![NamedPoly::new(
                "law",
                PolyExpr::prod(
                    rho.clone(),
                    PolyExpr::diff(rho, PolyExpr::rat(1, 1).unwrap()),
                ),
            )],
            provenance: Provenance::default(),
        }),
        provenance: Provenance::default(),
    })
    .unwrap();
    let out_obs = solve_observation_task(&task_obs);
    assert_eq!(out_obs.verdict, Verdict::Established);
    let det_obs = out_obs.observations.unwrap();
    assert!(det_obs.sufficient);
    assert_eq!(
        det_obs.minimal_sufficient_sets[0].observations,
        vec!["e_rho".to_owned()]
    );
    let lrc_obs = det_obs.law_readout_comparison.unwrap();
    assert!(lrc_obs.coarse_adequate_for_law_readout);
    assert!(!lrc_obs.coarse_adequate_for_decision);
}

#[test]
fn observation_silences_on_unobserved_slots_and_index_limit() {
    let mut fam = w4_obs_family();
    if let RealizationSpace::FiniteMembers(ref mut ms) = fam.realizations.space {
        ms[0]
            .assignments
            .insert("a".to_owned(), CoordValue::Missing);
    }
    let t_unobs = CheckedObservationTask::validate(ObservationTaskSpec {
        name: "obs_unobs".to_owned(),
        family: fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        observations: vec![],
        law_readout: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    assert!(matches!(
        solve_observation_task(&t_unobs).verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { .. })
    ));

    // > DEFAULT_MAX_OBS_INDICES (16) -> FiniteEnumerationOutOfScope
    let many_obs: Vec<CandidateObservationDecl> = (0..17)
        .map(|i| CandidateObservationDecl {
            id: format!("o{i}"),
            components: vec![NamedPoly::new("v", PolyExpr::param("a"))],
            cost: None,
            origin: src(&format!("o{i}"), OriginKind::StaticAnalysis),
        })
        .collect();
    let t_many = CheckedObservationTask::validate(ObservationTaskSpec {
        name: "obs_many".to_owned(),
        family: w4_obs_family(),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        observations: many_obs,
        law_readout: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    assert!(matches!(
        solve_observation_task(&t_many).verdict,
        Verdict::Undetermined(SilenceReason::FiniteEnumerationOutOfScope { .. })
    ));
}

#[test]
fn observation_scheme_zero_root_existential_rank2_and_realization_cap() {
    use crate::ir::presentation::{
        CoordDecl, ObservationDecl, OperationDecl, PhaseDecl, Presentation, SortDecl,
    };

    // 1. M5(1) + Existential: PolynomialScheme u*(u-1)=0 over AlgebraicClosure enumerates finitely [0, 1]
    // and Existential goodness w - u = 0 cleanly builds distinguishing pairs & finds {e_u}.
    let fam_scheme = FamilySpec {
        name: "ObsZeroRoot".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["u".to_owned()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![NamedPoly::new(
                    "bool_u",
                    PolyExpr::prod(
                        PolyExpr::param("u"),
                        PolyExpr::diff(PolyExpr::param("u"), PolyExpr::rat(1, 1).unwrap()),
                    ),
                )],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: src("zr-u", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec!["c".to_owned()],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".to_owned(),
                assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(0)))]),
                origin: src("c0", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Existential {
            witness_vars: vec!["w".to_owned()],
            equations: vec![
                NamedPoly::new("w0", PolyExpr::param("w")),
                NamedPoly::new(
                    "u_ok",
                    PolyExpr::diff(PolyExpr::param("u"), PolyExpr::param("c")),
                ),
            ],
            invertibles: vec![],
            preservation: None,
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };
    let t_zr = CheckedObservationTask::validate(ObservationTaskSpec {
        name: "obs_zr".to_owned(),
        family: fam_scheme,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        observations: vec![CandidateObservationDecl {
            id: "e_u".to_owned(),
            components: vec![NamedPoly::new("u_val", PolyExpr::param("u"))],
            cost: None,
            origin: src("e_u", OriginKind::StaticAnalysis),
        }],
        law_readout: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    let o_zr = solve_observation_task(&t_zr);
    assert_eq!(o_zr.verdict, Verdict::Established);
    let det_zr = o_zr.observations.unwrap();
    assert_eq!(det_zr.distinguishing_pair_count, 1);
    assert_eq!(
        det_zr.minimal_sufficient_sets[0].observations,
        vec!["e_u".to_owned()]
    );

    // 2. M7 sort.rank = 2 -> ApplicabilityConditionNotMet
    let mut fam_r2 = w4_obs_family();
    if let RealizationSpace::FiniteMembers(ref mut ms) = fam_r2.realizations.space {
        ms[0].presentation = Some(Presentation {
            name: "P_r2".to_owned(),
            coeff_domain: CoeffDomain::Q,
            sorts: vec![SortDecl {
                name: "S".to_owned(),
                rank: 2,
                coeff_domain: CoeffDomain::Q,
                provenance: None,
            }],
            phases: vec![PhaseDecl {
                name: "Idle".to_owned(),
                coords: vec![CoordDecl::symbolic("x", "S")],
                state_laws: vec![],
                provenance: None,
            }],
            operations: vec![OperationDecl {
                name: "nop".to_owned(),
                source_phase: "Idle".to_owned(),
                target_phase: "Idle".to_owned(),
                args: vec![],
                domain_laws: vec![],
                updates: BTreeMap::from([("x".to_owned(), PolyExpr::state("x"))]),
                provenance: None,
            }],
            observations: vec![ObservationDecl {
                name: "r".to_owned(),
                phase: "Idle".to_owned(),
                components: vec![PolyExpr::state("x")],
                provenance: None,
            }],
            provenance: Provenance::default(),
        });
    }
    let t_r2 = CheckedObservationTask::validate(ObservationTaskSpec {
        name: "obs_r2".to_owned(),
        family: fam_r2,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        observations: vec![],
        law_readout: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    assert!(matches!(
        solve_observation_task(&t_r2).verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { .. })
    ));

    // 3. > 256 realizations -> FiniteEnumerationOutOfScope
    let mut fam_cap = w4_obs_family();
    if let RealizationSpace::FiniteMembers(ref mut ms) = fam_cap.realizations.space {
        let base_m = ms[0].clone();
        *ms = (0..260)
            .map(|i| RealizationMember {
                id: format!("m_{i}"),
                ..base_m.clone()
            })
            .collect();
    }
    let t_cap = CheckedObservationTask::validate(ObservationTaskSpec {
        name: "obs_cap".to_owned(),
        family: fam_cap,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        observations: vec![],
        law_readout: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    assert!(matches!(
        solve_observation_task(&t_cap).verdict,
        Verdict::Undetermined(SilenceReason::FiniteEnumerationOutOfScope { .. })
    ));
}
