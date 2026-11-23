use super::*;
use crate::ir::change::{
    ChangeSpec, EditableTarget, FixedTarget, NamedPoly, ParamDecl, PointDomain,
};
use crate::ir::family::{
    CandidateFamilySpec, CandidateMember, CandidateSpace, CheckedFamilySpec, FamilySpec,
    GoodnessSpec, PreservationGoodnessSource, ReadingComparisonSpec, RealizationFamilySpec,
    RealizationMember, RealizationSpace,
};
use crate::ir::observation::{
    CandidateObservationDecl, CheckedObservationTask, ObservationTaskSpec,
};
use crate::ir::presentation::{
    ComparisonPair, CoordDecl, CoordValue, LawKind, OperationDecl, PhaseDecl, Presentation,
    SortDecl, StateComparison, StateLaw, TranslatedStep, TranslatedWord, WordTranslation,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::robustness::{
    CandidateSelector, CheckedChevalleyTask, CheckedRobustnessTask, ChevalleyTaskSpec,
    RobustnessTaskSpec,
};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::solver::family_eval::enumerate_realizations_for_base;
use std::collections::BTreeMap;

fn origin(id: &str) -> SourceRef {
    SourceRef::new(id, OriginKind::HumanAdopted).with_location(
        "regression-spec",
        "phase3_regressions.law",
        Some((1, 20)),
    )
}

fn prov(id: &str, clause: MathClause) -> Provenance {
    Provenance::new(vec![origin(id)], vec![clause])
}

fn z_lit(n: i64) -> ScalarLit {
    ScalarLit::int(n)
}

fn q_lit(n: i64) -> ScalarLit {
    ScalarLit::rat(n, 1).expect("denominator 1 is valid")
}

fn q_expr(n: i64) -> PolyExpr {
    PolyExpr::constant(q_lit(n))
}

fn fp_lit(v: i64, m: u64) -> ScalarLit {
    ScalarLit::fp(v.into(), m.into()).expect("valid modulus")
}

fn fp_expr(v: i64, m: u64) -> PolyExpr {
    PolyExpr::constant(fp_lit(v, m))
}

fn c1_empty_candidate_family(cand_space: CandidateSpace) -> FamilySpec {
    FamilySpec {
        name: "c1_empty_cb".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u_line".into(),
            u_vars: vec!["u".into()],
            b_vars: vec!["b".into()],
            reading_q: vec![q_expr(0)],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: origin("orig-u"),
            },
        },
        candidates: CandidateFamilySpec {
            name: "c_empty".into(),
            c_vars: vec!["c".into()],
            pi: vec![PolyExpr::param("c")],
            space: cand_space,
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
        reading_comparison: None,
        provenance: prov("orig-fam", MathClause::G140E4),
    }
}

#[test]
fn c1_infinite_u_with_empty_cb_refutes_pointwise_and_common() {
    let cases = [
        (
            "empty_finite_members",
            CandidateSpace::FiniteMembers(vec![]),
            PointDomain::AlgebraicClosure,
        ),
        (
            "mismatched_pi_fiber",
            CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c1".into(),
                assignments: BTreeMap::from([("c".into(), CoordValue::Observed(q_lit(1)))]),
                origin: origin("orig-c1"),
            }]),
            PointDomain::AlgebraicClosure,
        ),
    ];

    for (label, space, pt_dom) in cases {
        let task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
            name: format!("c1_{label}"),
            family: c1_empty_candidate_family(space),
            point_domain: pt_dom,
            base_value: vec![q_lit(0)],
            designated_candidate: None,
            check_universal_ring: false,
            fine_base_value: None,
            provenance: prov("orig-task", MathClause::G140E4),
        })
        .expect("task validates");

        let out = solve_robustness_task(&task);
        let detail = out.robustness.as_ref().expect("robustness detail");
        assert!(
            detail.fiber_non_empty.non_empty,
            "{label}: U_b must be non-empty"
        );
        assert_eq!(
            out.verdict,
            Verdict::Refuted,
            "{label}: empty C_b with non-empty U_b must refute"
        );
        let pw = detail.pointwise.as_ref().expect("pointwise result");
        assert!(!pw.satisfied, "{label}: pointwise must be false");
        assert!(
            pw.counterexample.is_some(),
            "{label}: pointwise must record witness u in U_b"
        );
        let cc = detail.common_candidate.as_ref().expect("common result");
        assert!(!cc.satisfied, "{label}: common candidate must be false");
    }
}

fn c2_z_domain_rational_root_family(good_expr: PolyExpr, eq_expr: PolyExpr) -> FamilySpec {
    FamilySpec {
        name: "c2_z_rat_root".into(),
        coeff_domain: CoeffDomain::Z,
        realizations: RealizationFamilySpec {
            name: "u_scheme".into(),
            u_vars: vec!["u".into()],
            b_vars: vec!["b".into()],
            reading_q: vec![PolyExpr::int(0)],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![NamedPoly::new("u_eq", eq_expr)],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: origin("orig-u"),
            },
        },
        candidates: CandidateFamilySpec {
            name: "c_fixed".into(),
            c_vars: vec!["c".into()],
            pi: vec![PolyExpr::int(0)],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c_one".into(),
                assignments: BTreeMap::from([("c".into(), CoordValue::Observed(z_lit(1)))]),
                origin: origin("orig-c1"),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new("ok", good_expr)],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: prov("orig-fam", MathClause::G140E4),
    }
}

#[test]
fn c2_z_coeff_domain_preserves_rational_solutions_without_truncation_or_panic() {
    // 2u - 1 = 0 has rational solution u = 1/2 (not truncated to 0); u - c != 0 when c = 1.
    let eq_half = PolyExpr::diff(
        PolyExpr::prod(PolyExpr::int(2), PolyExpr::param("u")),
        PolyExpr::int(1),
    );
    let good_eq_c = PolyExpr::diff(PolyExpr::param("u"), PolyExpr::param("c"));
    for pt_dom in [PointDomain::RationalPoints, PointDomain::AlgebraicClosure] {
        let task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
            name: "c2_linear_half".into(),
            family: c2_z_domain_rational_root_family(good_eq_c.clone(), eq_half.clone()),
            point_domain: pt_dom,
            base_value: vec![z_lit(0)],
            designated_candidate: Some(CandidateSelector::ById("c_one".into())),
            check_universal_ring: false,
            fine_base_value: None,
            provenance: prov("orig-task", MathClause::G140E4),
        })
        .expect("task validates");
        let out = solve_robustness_task(&task);
        assert_eq!(out.verdict, Verdict::Refuted);
        let detail = out.robustness.as_ref().unwrap();
        assert!(detail.fiber_non_empty.non_empty);
        let ce = detail
            .valid_designated
            .as_ref()
            .and_then(|v| v.counterexample.as_ref())
            .expect("counterexample at u = 1/2");
        assert_eq!(
            ce.realization.assignments.get("u").map(String::as_str),
            Some("1/2")
        );
    }

    // 2u^2 - 3u + 1 = (2u - 1)(u - 1) = 0: u = 1 passes u - c = 0 (c = 1), u = 1/2 fails.
    let eq_quad = PolyExpr::sum(
        PolyExpr::diff(
            PolyExpr::prod(PolyExpr::int(2), PolyExpr::pow(PolyExpr::param("u"), 2)),
            PolyExpr::prod(PolyExpr::int(3), PolyExpr::param("u")),
        ),
        PolyExpr::int(1),
    );
    for pt_dom in [PointDomain::RationalPoints, PointDomain::AlgebraicClosure] {
        let obs_task = CheckedObservationTask::validate(ObservationTaskSpec {
            name: "c2_obs_quad".into(),
            family: c2_z_domain_rational_root_family(good_eq_c.clone(), eq_quad.clone()),
            point_domain: pt_dom,
            base_value: vec![z_lit(0)],
            observations: vec![CandidateObservationDecl {
                id: "e_u".into(),
                components: vec![NamedPoly::new("u_obs", PolyExpr::param("u"))],
                cost: None,
                origin: origin("orig-e"),
            }],
            law_readout: None,
            provenance: prov("orig-obs", MathClause::G142G5),
        })
        .expect("obs task validates");
        let out = solve_observation_task(&obs_task);
        assert_eq!(out.verdict, Verdict::Established);
        let obs = out.observations.as_ref().unwrap();
        assert!(obs.sufficient);
        assert_eq!(obs.distinguishing_pair_count, 1);
        assert_eq!(obs.minimal_sufficient_sets[0].observations, vec!["e_u"]);
    }
}

#[test]
fn c3_universal_ring_point_domain_fails_closed_everywhere() {
    let fam_fp = FamilySpec {
        name: "c3_fp".into(),
        coeff_domain: CoeffDomain::Fp(5u32.into()),
        realizations: RealizationFamilySpec {
            name: "u_fp".into(),
            u_vars: vec!["u".into()],
            b_vars: vec!["b".into()],
            reading_q: vec![fp_expr(0, 5)],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![NamedPoly::new(
                    "frobenius",
                    PolyExpr::diff(PolyExpr::pow(PolyExpr::param("u"), 5), PolyExpr::param("u")),
                )],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: origin("orig-u"),
            },
        },
        candidates: CandidateFamilySpec {
            name: "c_fp".into(),
            c_vars: vec!["c".into()],
            pi: vec![fp_expr(0, 5)],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".into(),
                assignments: BTreeMap::from([("c".into(), CoordValue::Observed(fp_lit(0, 5)))]),
                origin: origin("orig-c0"),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new("ok", PolyExpr::param("c"))],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: prov("orig-fam", MathClause::G140E5),
    };

    let checked_fp = CheckedFamilySpec::validate(fam_fp.clone()).expect("family validates");
    let enum_err = enumerate_realizations_for_base(
        &checked_fp,
        &[fp_lit(0, 5)],
        &PointDomain::UniversalRing,
        64,
    )
    .expect_err("enumerate must fail closed for UniversalRing");
    assert!(matches!(
        enum_err,
        SilenceReason::UniversalRingOutOfScope { .. }
    ));

    let rob_fp = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "c3_rob_fp".into(),
        family: fam_fp.clone(),
        point_domain: PointDomain::UniversalRing,
        base_value: vec![fp_lit(0, 5)],
        designated_candidate: None,
        check_universal_ring: true,
        fine_base_value: None,
        provenance: prov("orig-task", MathClause::G140E5),
    })
    .expect("robustness task validates");
    let rob_out = solve_robustness_task(&rob_fp);
    assert!(matches!(
        rob_out.verdict,
        Verdict::Undetermined(SilenceReason::UniversalRingOutOfScope { .. })
    ));

    let obs_fp = CheckedObservationTask::validate(ObservationTaskSpec {
        name: "c3_obs_fp".into(),
        family: fam_fp,
        point_domain: PointDomain::UniversalRing,
        base_value: vec![fp_lit(0, 5)],
        observations: vec![CandidateObservationDecl {
            id: "e0".into(),
            components: vec![NamedPoly::new("u_obs", PolyExpr::param("u"))],
            cost: None,
            origin: origin("orig-e0"),
        }],
        law_readout: None,
        provenance: prov("orig-obs", MathClause::G142G5),
    })
    .expect("observation task validates");
    let obs_out = solve_observation_task(&obs_fp);
    assert!(matches!(
        obs_out.verdict,
        Verdict::Undetermined(SilenceReason::UniversalRingOutOfScope { .. })
    ));

    // Also verify Q-domain UniversalRing fails closed in robustness.
    let mut fam_q =
        c1_empty_candidate_family(CandidateSpace::FiniteMembers(vec![CandidateMember {
            id: "c0".into(),
            assignments: BTreeMap::from([("c".into(), CoordValue::Observed(q_lit(0)))]),
            origin: origin("orig-c0"),
        }]));
    fam_q.realizations.space = RealizationSpace::PolynomialScheme {
        equations: vec![NamedPoly::new(
            "double_root",
            PolyExpr::pow(PolyExpr::diff(PolyExpr::param("u"), q_expr(1)), 2),
        )],
        invertibles: vec![],
        is_raw_candidate: false,
        origin: origin("orig-u"),
    };
    let rob_q = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "c3_rob_q".into(),
        family: fam_q,
        point_domain: PointDomain::UniversalRing,
        base_value: vec![q_lit(0)],
        designated_candidate: None,
        check_universal_ring: true,
        fine_base_value: None,
        provenance: prov("orig-task", MathClause::G140E5),
    })
    .expect("q task validates");
    let rob_q_out = solve_robustness_task(&rob_q);
    assert!(matches!(
        rob_q_out.verdict,
        Verdict::Undetermined(SilenceReason::UniversalRingOutOfScope { .. })
    ));
}

fn nc1_z_quotient_preservation_source(witness_param: Option<&str>) -> PreservationGoodnessSource {
    let orig = origin("orig-pres");
    let mut after_laws = vec![StateLaw {
        name: "rep_quot".into(),
        kind: LawKind::Representation,
        polynomial: PolyExpr::diff(PolyExpr::state("x"), PolyExpr::int(1)),
        provenance: None,
    }];
    let mut params = vec![ParamDecl {
        name: "delta".into(),
        coeff_domain: CoeffDomain::Z,
        provenance: None,
    }];
    let mut param_bindings = BTreeMap::from([("delta".into(), PolyExpr::param("u"))]);
    if let Some(w_var) = witness_param {
        params.push(ParamDecl {
            name: w_var.into(),
            coeff_domain: CoeffDomain::Z,
            provenance: None,
        });
        param_bindings.insert(w_var.into(), PolyExpr::param(w_var));
        after_laws[0].polynomial = PolyExpr::prod(PolyExpr::param(w_var), PolyExpr::state("x"));
    }

    let mk_pres = |name: &str, laws: Vec<StateLaw>| Presentation {
        name: name.into(),
        coeff_domain: CoeffDomain::Z,
        sorts: vec![SortDecl {
            name: "D".into(),
            rank: 1,
            coeff_domain: CoeffDomain::Z,
            provenance: Some(orig.clone()),
        }],
        phases: vec![PhaseDecl {
            name: "S".into(),
            coords: vec![CoordDecl::symbolic("x", "D")],
            state_laws: laws,
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "step".into(),
            source_phase: "S".into(),
            target_phase: "S".into(),
            args: vec![],
            domain_laws: vec![],
            updates: BTreeMap::from([("x".into(), PolyExpr::state("x"))]),
            provenance: None,
        }],
        observations: vec![],
        provenance: prov("orig-pres", MathClause::G140P3P5),
    };

    let before = mk_pres("BeforeZ", vec![]);
    let after = mk_pres("AfterZ", after_laws);
    let pair = ComparisonPair {
        before,
        after,
        state_comparisons: vec![StateComparison {
            after_phase: "S".into(),
            before_phase: "S".into(),
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
        name: "ChgZ".into(),
        coeff_domain: CoeffDomain::Z,
        parameters: params,
        fixed: vec![
            FixedTarget::StateComparisonExpr {
                after_phase: "S".into(),
            },
            FixedTarget::WordTranslationOp {
                operation: "step".into(),
            },
        ],
        editable: vec![EditableTarget::OperationExpr {
            presentation: "AfterZ".into(),
            operation: "step".into(),
        }],
        provenance: prov("orig-chg", MathClause::G140E1E2),
    };

    PreservationGoodnessSource {
        pair,
        change_spec,
        param_bindings,
    }
}

#[test]
fn nc1_z_rational_quotient_preservation_fails_closed() {
    for is_existential in [false, true] {
        let goodness = if is_existential {
            GoodnessSpec::Existential {
                witness_vars: vec!["w".into()],
                equations: vec![],
                invertibles: vec![],
                preservation: Some(nc1_z_quotient_preservation_source(Some("w"))),
            }
        } else {
            GoodnessSpec::Direct {
                equations: vec![],
                invertibles: vec![],
                preservation: Some(nc1_z_quotient_preservation_source(None)),
                raw_sequence: None,
            }
        };

        let fam = FamilySpec {
            name: "nc1_z_quot".into(),
            coeff_domain: CoeffDomain::Z,
            realizations: RealizationFamilySpec {
                name: "r_z".into(),
                u_vars: vec!["u".into()],
                b_vars: vec!["b".into()],
                reading_q: vec![PolyExpr::int(0)],
                space: RealizationSpace::FiniteMembers(vec![RealizationMember {
                    id: "u0".into(),
                    assignments: BTreeMap::from([("u".into(), CoordValue::Observed(z_lit(0)))]),
                    is_raw_candidate: false,
                    presentation: None,
                    origin: origin("orig-u0"),
                }]),
            },
            candidates: CandidateFamilySpec {
                name: "c_z".into(),
                c_vars: vec!["c".into()],
                pi: vec![PolyExpr::int(0)],
                space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                    id: "c0".into(),
                    assignments: BTreeMap::from([("c".into(), CoordValue::Observed(z_lit(0)))]),
                    origin: origin("orig-c0"),
                }]),
            },
            goodness,
            reading_comparison: None,
            provenance: prov("orig-fam", MathClause::G140E4),
        };

        let task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
            name: if is_existential {
                "nc1_existential"
            } else {
                "nc1_direct"
            }
            .into(),
            family: fam,
            point_domain: PointDomain::RationalPoints,
            base_value: vec![z_lit(0)],
            designated_candidate: Some(CandidateSelector::ById("c0".into())),
            check_universal_ring: false,
            fine_base_value: None,
            provenance: prov("orig-task", MathClause::G140E4),
        })
        .expect("task validates");
        let out = solve_robustness_task(&task);
        assert!(
            matches!(
                out.verdict,
                Verdict::Undetermined(SilenceReason::QuotientIdealOutOfScope { .. })
            ),
            "existential={is_existential} got {:?}",
            out.verdict
        );
    }
}

#[test]
fn nc2_rational_existential_unconstrained_invertible_witness_established() {
    let fam = FamilySpec {
        name: "nc2_unconstrained_inv".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "r_q".into(),
            u_vars: vec!["u".into()],
            b_vars: vec!["b".into()],
            reading_q: vec![q_expr(0)],
            space: RealizationSpace::FiniteMembers(vec![RealizationMember {
                id: "u0".into(),
                assignments: BTreeMap::from([("u".into(), CoordValue::Observed(q_lit(1)))]),
                is_raw_candidate: false,
                presentation: None,
                origin: origin("orig-u0"),
            }]),
        },
        candidates: CandidateFamilySpec {
            name: "c_q".into(),
            c_vars: vec!["c".into()],
            pi: vec![q_expr(0)],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".into(),
                assignments: BTreeMap::from([("c".into(), CoordValue::Observed(q_lit(1)))]),
                origin: origin("orig-c0"),
            }]),
        },
        goodness: GoodnessSpec::Existential {
            witness_vars: vec!["w".into()],
            equations: vec![],
            invertibles: vec![NamedPoly::new("w_nz", PolyExpr::param("w"))],
            preservation: None,
        },
        reading_comparison: None,
        provenance: prov("orig-fam", MathClause::G140E4),
    };

    let task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "nc2_task".into(),
        family: fam,
        point_domain: PointDomain::RationalPoints,
        base_value: vec![q_lit(0)],
        designated_candidate: Some(CandidateSelector::ById("c0".into())),
        check_universal_ring: false,
        fine_base_value: None,
        provenance: prov("orig-task", MathClause::G140E4),
    })
    .expect("task validates");
    let out = solve_robustness_task(&task);
    assert_eq!(out.verdict, Verdict::Established);
    let vd = out
        .robustness
        .as_ref()
        .unwrap()
        .valid_designated
        .as_ref()
        .unwrap();
    assert!(vd.satisfied);
    let rc = vd
        .supporting_witnesses
        .first()
        .expect("supporting witness present")
        .restored_completion
        .as_ref()
        .unwrap();
    assert!(rc.reeval.matched);
    assert_ne!(
        rc.witness_assignments.get("w").map(String::as_str),
        Some("0")
    );
}

#[test]
fn nc3_chevalley_irrational_universal_silence_and_multi_stratum_mixed() {
    // Part A (NC3(2)): irrational candidate scheme c^2 - 2 = 0 with check_universal_ring: true
    // and designated_candidate: None -> universal_ring_contrast fails closed (UniversalRingOutOfScope).
    let mut fam_a = c1_empty_candidate_family(CandidateSpace::PolynomialScheme {
        equations: vec![NamedPoly::new(
            "c_irrat",
            PolyExpr::diff(PolyExpr::pow(PolyExpr::param("c"), 2), q_expr(2)),
        )],
        invertibles: vec![],
        origin: origin("orig-cs-a"),
    });
    fam_a.candidates.pi = vec![q_expr(0)];
    fam_a.goodness = GoodnessSpec::Direct {
        equations: vec![NamedPoly::new("ok", q_expr(0))],
        invertibles: vec![],
        preservation: None,
        raw_sequence: None,
    };
    let task_a = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "nc3_part_a_irrat_universal".into(),
        family: fam_a,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: Some(vec![q_lit(0)]),
        designated_candidate: None,
        rational_fiber_probes: vec![],
        check_global_regular_section: false,
        check_universal_ring: true,
        provenance: prov("orig-chev-a", MathClause::G141D7),
    })
    .expect("part A task validates");

    let out_a = solve_chevalley_task(&task_a);
    let chev_a = out_a.chevalley.as_ref().expect("part A chevalley detail");
    let ur_a = chev_a
        .universal_ring_contrast
        .as_ref()
        .expect("universal_ring_contrast must be Some for irrational candidate scheme");
    assert!(!ur_a.evaluated);
    assert_eq!(ur_a.stable, None);
    assert!(matches!(
        ur_a.silence_reason,
        Some(SilenceReason::UniversalRingOutOfScope { .. })
    ));

    // Part B (NC3(1)): multi-stratum `mixed` where D(c - 1) holds only irrational c^2 - 2 = 0
    // while V(c - 1) holds rational c = 1 with passing u = 1 and failing u = 0.
    let fam_b = FamilySpec {
        name: "nc3_part_b_multi_stratum".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u_two_pts".into(),
            u_vars: vec!["u".into()],
            b_vars: vec!["b".into()],
            reading_q: vec![q_expr(0)],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![NamedPoly::new(
                    "u_or_branch",
                    PolyExpr::prod(
                        PolyExpr::param("u"),
                        PolyExpr::diff(PolyExpr::param("u"), q_expr(1)),
                    ),
                )],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: origin("orig-us-b"),
            },
        },
        candidates: CandidateFamilySpec {
            name: "c_split".into(),
            c_vars: vec!["c".into()],
            pi: vec![q_expr(0)],
            space: CandidateSpace::PolynomialScheme {
                equations: vec![NamedPoly::new(
                    "c_branch",
                    PolyExpr::prod(
                        PolyExpr::diff(PolyExpr::pow(PolyExpr::param("c"), 2), q_expr(2)),
                        PolyExpr::diff(PolyExpr::param("c"), q_expr(1)),
                    ),
                )],
                invertibles: vec![],
                origin: origin("orig-cs-b"),
            },
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new(
                "ok_mixed",
                PolyExpr::prod(
                    PolyExpr::param("u"),
                    PolyExpr::diff(PolyExpr::param("c"), q_expr(1)),
                ),
            )],
            invertibles: vec![NamedPoly::new(
                "ok_inv",
                PolyExpr::sum(
                    PolyExpr::diff(PolyExpr::param("c"), q_expr(1)),
                    PolyExpr::param("u"),
                ),
            )],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: prov("orig-fam-b", MathClause::G141D7),
    };

    let task_b = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "nc3_part_b_mixed".into(),
        family: fam_b,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: Some(vec![q_lit(0)]),
        designated_candidate: None,
        rational_fiber_probes: vec![],
        check_global_regular_section: false,
        check_universal_ring: false,
        provenance: prov("orig-chev-b", MathClause::G141D7),
    })
    .expect("part B task validates");

    let out_b = solve_chevalley_task(&task_b);
    let chev_b = out_b.chevalley.as_ref().expect("part B chevalley detail");
    assert!(!chev_b.mixed.is_empty);
    assert!(
        chev_b.mixed.strata.len() >= 2,
        "expected >= 2 strata in mixed, got {:?}",
        chev_b.mixed.strata
    );
    assert!(chev_b.mixed_witness_pair.is_some());
}

#[test]
fn nc4_empty_fiber_checks_reading_commutativity_and_vacuous_fine_fiber() {
    // NC4(1): Empty U_b with non-commutative reading_comparison must fail closed with ApplicabilityConditionNotMet.
    let non_comm_fam = FamilySpec {
        name: "nc4_non_comm".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u_empty".into(),
            u_vars: vec!["u".into()],
            b_vars: vec!["b".into()],
            reading_q: vec![PolyExpr::param("u")],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![
                    NamedPoly::new("e1", PolyExpr::diff(PolyExpr::param("u"), q_expr(1))),
                    NamedPoly::new("e2", PolyExpr::diff(PolyExpr::param("u"), q_expr(2))),
                ],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: origin("orig-u"),
            },
        },
        candidates: CandidateFamilySpec {
            name: "c_one".into(),
            c_vars: vec!["c".into()],
            pi: vec![PolyExpr::param("c")],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c1".into(),
                assignments: BTreeMap::from([("c".into(), CoordValue::Observed(q_lit(1)))]),
                origin: origin("orig-c1"),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new("ok", q_expr(0))],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: Some(ReadingComparisonSpec {
            name: "bad_rc".into(),
            fine_b_vars: vec!["bf".into()],
            fine_q: vec![PolyExpr::sum(PolyExpr::param("u"), q_expr(1))],
            coarsen_r: vec![PolyExpr::param("bf")], // r(fine_q(u)) = u + 1 != q(u) = u
            provenance: prov("orig-rc", MathClause::G140E5Dot1),
        }),
        provenance: prov("orig-fam", MathClause::G140E5Dot1),
    };
    let task1 = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "nc4_non_comm_empty_u".into(),
        family: non_comm_fam,
        point_domain: PointDomain::RationalPoints,
        base_value: vec![q_lit(1)],
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: Some(vec![q_lit(2)]),
        provenance: prov("orig-task", MathClause::G140E5Dot1),
    })
    .expect("task1 validates");
    let out1 = solve_robustness_task(&task1);
    assert!(matches!(
        &out1.verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { condition, .. })
            if condition == "reading_comparison_commutes"
    ));

    // NC4(2): coarse_robust == true with empty fine sub-fiber U_{b'} and non-empty C_b preserves implication.
    let vac_fine_fam = FamilySpec {
        name: "nc4_vac_fine".into(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "u_single".into(),
            u_vars: vec!["u".into()],
            b_vars: vec!["b".into()],
            reading_q: vec![q_expr(0)],
            space: RealizationSpace::FiniteMembers(vec![RealizationMember {
                id: "u0".into(),
                assignments: BTreeMap::from([("u".into(), CoordValue::Observed(q_lit(0)))]),
                is_raw_candidate: false,
                presentation: None,
                origin: origin("orig-u0"),
            }]),
        },
        candidates: CandidateFamilySpec {
            name: "c_single".into(),
            c_vars: vec!["c".into()],
            pi: vec![q_expr(0)],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".into(),
                assignments: BTreeMap::from([("c".into(), CoordValue::Observed(q_lit(0)))]),
                origin: origin("orig-c0"),
            }]),
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
            name: "fine_rc".into(),
            fine_b_vars: vec!["bf".into()],
            fine_q: vec![PolyExpr::param("u")],
            coarsen_r: vec![q_expr(0)],
            provenance: prov("orig-rc", MathClause::G142G4),
        }),
        provenance: prov("orig-fam", MathClause::G142G4),
    };
    let task2 = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "nc4_vac_fine_task".into(),
        family: vac_fine_fam,
        point_domain: PointDomain::RationalPoints,
        base_value: vec![q_lit(0)],
        designated_candidate: Some(CandidateSelector::ById("c0".into())),
        check_universal_ring: false,
        fine_base_value: Some(vec![q_lit(1)]), // fine fiber U_{bf=1} is empty while U_{b=0} = {u=0}
        provenance: prov("orig-task", MathClause::G142G4),
    })
    .expect("task2 validates");
    let out2 = solve_robustness_task(&task2);
    assert_eq!(out2.verdict, Verdict::Established);
    let rc_res = out2
        .robustness
        .as_ref()
        .unwrap()
        .reading_comparison
        .as_ref()
        .expect("reading comparison present");
    assert!(rc_res.commutativity_verified);
    assert!(rc_res.coarse_robust);
    assert!(rc_res.fine_robust);
    assert!(rc_res.coarse_implies_fine_preserved);
}
