//! PR #6437 査読指摘（M3・M4・M5・M6・M7・P7 違法列・AC6 追加境界）の回帰・検証テスト。

use crate::ir::change::{ChangeSpec, EditableTarget, NamedPoly, ParamDecl, PointDomain};
use crate::ir::family::{
    CandidateFamilySpec, CandidateMember, CandidateSpace, FamilySpec, GoodnessSpec,
    PreservationGoodnessSource, RawSequenceCheck, ReadingComparisonSpec, RealizationFamilySpec,
    RealizationMember, RealizationSpace,
};
use crate::ir::presentation::{
    ComparisonPair, CoordDecl, CoordValue, LawKind, ObservationDecl, OperationDecl, PhaseDecl,
    Presentation, SortDecl, StateComparison, StateLaw, TranslatedStep, TranslatedWord,
    WordTranslation,
};
use crate::ir::provenance::{OriginKind, Provenance, SourceRef};
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

fn z(n: i64) -> ScalarLit {
    ScalarLit::int(n)
}

fn fp(val: u32, p: u32) -> ScalarLit {
    ScalarLit::Fp {
        value: val.into(),
        modulus: p.into(),
    }
}

#[test]
fn m3_universal_ring_evaluates_multiple_candidates_and_silences_on_scheme_without_designated() {
    // W6 scheme + 2 candidates (neither is universally stable over Q[eps]/(eps^2)):
    // even with designated_candidate: None, check_universal_ring: true must refute (never skip to Established).
    let rho_m1 = PolyExpr::diff(PolyExpr::param("rho"), PolyExpr::rat(1, 1).unwrap());
    let two_cand_w6 = FamilySpec {
        name: "W6TwoCand".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["rho".to_owned()],
            b_vars: vec!["b".to_owned()],
            reading_q: vec![PolyExpr::pow(rho_m1.clone(), 2)],
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
            space: CandidateSpace::FiniteMembers(vec![
                CandidateMember {
                    id: "c0".to_owned(),
                    assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(0)))]),
                    origin: src("c0", OriginKind::HumanAdopted),
                },
                CandidateMember {
                    id: "c0_dup".to_owned(),
                    assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(0)))]),
                    origin: src("c0-dup", OriginKind::RuntimeObservation),
                },
            ]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new(
                "unipotent_trivial",
                PolyExpr::sum(rho_m1, PolyExpr::param("c")),
            )],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };
    let t_two = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "w6_two_cand".to_owned(),
        family: two_cand_w6.clone(),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![q(0)],
        designated_candidate: None,
        check_universal_ring: true,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    let o_two = solve_robustness_task(&t_two);
    assert_eq!(o_two.verdict, Verdict::Refuted);
    let ur = o_two
        .robustness
        .unwrap()
        .universal_ring
        .expect("ur checked");
    assert_eq!(ur.stable, Some(false));
    assert!(ur.dual_number_counterexample.is_some());

    // NonFiniteScheme candidate space + designated: None + check_universal_ring: true -> Undetermined(UniversalRingOutOfScope)
    let mut scheme_cand = two_cand_w6;
    scheme_cand.realizations.b_vars.clear();
    scheme_cand.realizations.reading_q.clear();
    scheme_cand.candidates.pi.clear();
    scheme_cand.candidates.space = CandidateSpace::PolynomialScheme {
        equations: vec![],
        invertibles: vec![],
        origin: src("c-scheme", OriginKind::StaticAnalysis),
    };
    let t_scheme = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "w6_scheme_cand".to_owned(),
        family: scheme_cand,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        designated_candidate: None,
        check_universal_ring: true,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    assert!(matches!(
        solve_robustness_task(&t_scheme).verdict,
        Verdict::Undetermined(SilenceReason::UniversalRingOutOfScope { .. })
    ));
}

#[test]
fn m4_symbolic_existential_restores_concrete_witness_with_reeval_or_silences() {
    let shift_pres = |name: &str, step_expr: PolyExpr| Presentation {
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
                PolyExpr::sum(PolyExpr::state("x"), step_expr),
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
        name: "SymExist".to_owned(),
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
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".to_owned(),
                assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(2)))]),
                origin: src("c0", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Existential {
            witness_vars: vec!["w".to_owned()],
            equations: vec![NamedPoly::new(
                "lin",
                PolyExpr::diff(PolyExpr::param("w"), PolyExpr::param("c")),
            )],
            invertibles: vec![],
            preservation: Some(PreservationGoodnessSource {
                pair: ComparisonPair {
                    before: shift_pres("Before", PolyExpr::rat(2, 1).unwrap()),
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
        name: "sym_exist".to_owned(),
        family: fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        designated_candidate: Some(CandidateSelector::ById("c0".to_owned())),
        check_universal_ring: false,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    let out = solve_robustness_task(&task);
    assert_eq!(out.verdict, Verdict::Established);
    let det = out.robustness.unwrap();
    let vd = det.valid_designated.unwrap();
    assert!(!vd.supporting_witnesses.is_empty());
    let rc = vd.supporting_witnesses[0]
        .restored_completion
        .as_ref()
        .expect("restored completion required on Established existential");
    assert!(rc.reeval.matched);
    assert_eq!(
        rc.witness_assignments.get("w").map(String::as_str),
        Some("2")
    );
    assert!(!det.pointwise.unwrap().witnesses.is_empty());
    assert!(!det.common_candidate.unwrap().witnesses.is_empty());

    // Irrational scheme u^2 - 2 = 0 with Existential -> must silence rather than return Established without witness
    let irr_fam = FamilySpec {
        name: "IrrExist".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["u".to_owned()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![NamedPoly::new(
                    "irr",
                    PolyExpr::diff(
                        PolyExpr::pow(PolyExpr::param("u"), 2),
                        PolyExpr::rat(2, 1).unwrap(),
                    ),
                )],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: src("irr-u", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec!["c".to_owned()],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".to_owned(),
                assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(1)))]),
                origin: src("c0", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Existential {
            witness_vars: vec!["w".to_owned()],
            equations: vec![NamedPoly::new(
                "w_eq_u",
                PolyExpr::diff(PolyExpr::param("w"), PolyExpr::param("u")),
            )],
            invertibles: vec![],
            preservation: None,
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };
    let irr_task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "irr_exist".to_owned(),
        family: irr_fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        designated_candidate: Some(CandidateSelector::ById("c0".to_owned())),
        check_universal_ring: false,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    assert!(matches!(
        solve_robustness_task(&irr_task).verdict,
        Verdict::Undetermined(SilenceReason::NonLinearRationalOrIntegerExistence { .. })
    ));
}

#[test]
fn m5_rational_root_zero_exhausted_z_invertible_and_z_bounded_search() {
    // 1. M5(1): u * (u - 1) = 0 over AlgebraicClosure must enumerate finitely [0, 1] -> Existential restores!
    let zero_root_fam = FamilySpec {
        name: "ZeroRootScheme".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["u".to_owned()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![NamedPoly::new(
                    "u_bool",
                    PolyExpr::prod(
                        PolyExpr::param("u"),
                        PolyExpr::diff(PolyExpr::param("u"), PolyExpr::rat(1, 1).unwrap()),
                    ),
                )],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: src("zroot-u", OriginKind::StaticAnalysis),
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
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new(
                "bool_ok",
                PolyExpr::prod(
                    PolyExpr::param("u"),
                    PolyExpr::diff(PolyExpr::param("u"), PolyExpr::rat(1, 1).unwrap()),
                ),
            )],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };
    let zroot_task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "zero_root".to_owned(),
        family: zero_root_fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![],
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    let zroot_out = solve_robustness_task(&zroot_task);
    assert_eq!(zroot_out.verdict, Verdict::Established);
    let cm = zroot_out.robustness.unwrap().common_candidate.unwrap();
    // Finite path populates concrete evaluation witnesses for BOTH u=0 and u=1!
    assert_eq!(cm.witnesses.len(), 2);

    // 2. M5(3): 0-var scheme over CoeffDomain::Z / IntegerPoints with invertible [2] must be empty (not a Z-unit!)
    let zero_var_z = FamilySpec {
        name: "ZeroVarZUnit".to_owned(),
        coeff_domain: CoeffDomain::Z,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec![],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![],
                invertibles: vec![NamedPoly::new("nonunit2", PolyExpr::constant(z(2)))],
                is_raw_candidate: false,
                origin: src("zvz-u", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec![],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![]),
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
    let zvz_task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "zvz".to_owned(),
        family: zero_var_z,
        point_domain: PointDomain::IntegerPoints,
        base_value: vec![],
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    let zvz_out = solve_robustness_task(&zvz_task);
    assert_eq!(zvz_out.verdict, Verdict::Refuted);
    assert!(!zvz_out.robustness.unwrap().fiber_non_empty.non_empty);

    // 3. M5(2): IntegerPoints unconstrained existential witness with invertible [w - 100] (solution 101 > 64)
    // must return Undetermined(FiniteEnumerationOutOfScope), never Refuted!
    let box_z_fam = FamilySpec {
        name: "ZBoxLimit".to_owned(),
        coeff_domain: CoeffDomain::Z,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["u".to_owned()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::FiniteMembers(vec![RealizationMember {
                id: "u0".to_owned(),
                assignments: BTreeMap::from([("u".to_owned(), CoordValue::Observed(z(0)))]),
                is_raw_candidate: false,
                presentation: None,
                origin: src("u0", OriginKind::StaticAnalysis),
            }]),
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec!["c".to_owned()],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".to_owned(),
                assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(z(0)))]),
                origin: src("c0", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Existential {
            witness_vars: vec!["w".to_owned()],
            equations: vec![],
            invertibles: vec![NamedPoly::new(
                "w_m100",
                PolyExpr::diff(PolyExpr::param("w"), PolyExpr::constant(z(100))),
            )],
            preservation: None,
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };
    let box_task = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "z_box".to_owned(),
        family: box_z_fam,
        point_domain: PointDomain::IntegerPoints,
        base_value: vec![],
        designated_candidate: Some(CandidateSelector::ById("c0".to_owned())),
        check_universal_ring: false,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    assert!(matches!(
        solve_robustness_task(&box_task).verdict,
        Verdict::Undetermined(SilenceReason::FiniteEnumerationOutOfScope { .. })
    ));
}

#[test]
fn m6_fp_non_commutativity_and_nonfinite_fine_reading_comparison() {
    // 1. F_5 non-commutative PolynomialScheme must silence with ApplicabilityConditionNotMet
    let mut fp_nc_fam = FamilySpec {
        name: "FpNonComm".to_owned(),
        coeff_domain: CoeffDomain::Fp(5u32.into()),
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["x".to_owned()],
            b_vars: vec!["b".to_owned()],
            reading_q: vec![PolyExpr::sum(
                PolyExpr::param("x"),
                PolyExpr::constant(fp(1, 5)),
            )],
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
            equations: vec![],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: Some(ReadingComparisonSpec {
            name: "non_comm".to_owned(),
            fine_b_vars: vec!["fx".to_owned()],
            fine_q: vec![PolyExpr::param("x")],
            coarsen_r: vec![PolyExpr::param("fx")],
            provenance: Provenance::default(),
        }),
        provenance: Provenance::default(),
    };
    let t_nc = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "fp_nc".to_owned(),
        family: fp_nc_fam.clone(),
        point_domain: PointDomain::FiniteFieldPoints(5u32.into()),
        base_value: vec![fp(0, 5)],
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: Some(vec![fp(0, 5)]),
        provenance: Provenance::default(),
    })
    .unwrap();
    assert!(matches!(
        solve_robustness_task(&t_nc).verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { .. })
    ));

    // 2. NonFiniteScheme over Q with fine_base_value computes fine_robust accurately:
    // coarse: q(x, y) = x + y = 1 (allows arbitrary x, goodness x - 1 = 0 fails -> coarse_robust = false)
    // fine:   fine_q = [x, y] = [1, 0] (forces x = 1, y = 0 -> x - 1 = 0 holds -> fine_robust = true!)
    fp_nc_fam.name = "SchemeFine".to_owned();
    fp_nc_fam.coeff_domain = CoeffDomain::Q;
    fp_nc_fam.realizations.u_vars = vec!["x".to_owned(), "y".to_owned()];
    fp_nc_fam.realizations.reading_q =
        vec![PolyExpr::sum(PolyExpr::param("x"), PolyExpr::param("y"))];
    fp_nc_fam.candidates = CandidateFamilySpec {
        name: "C".to_owned(),
        c_vars: vec!["c".to_owned()],
        pi: vec![PolyExpr::param("c")],
        space: CandidateSpace::FiniteMembers(vec![CandidateMember {
            id: "c1".to_owned(),
            assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(1)))]),
            origin: src("c1", OriginKind::HumanAdopted),
        }]),
    };
    fp_nc_fam.goodness = GoodnessSpec::Direct {
        equations: vec![NamedPoly::new(
            "x_eq_1",
            PolyExpr::diff(PolyExpr::param("x"), PolyExpr::rat(1, 1).unwrap()),
        )],
        invertibles: vec![],
        preservation: None,
        raw_sequence: None,
    };
    fp_nc_fam.reading_comparison = Some(ReadingComparisonSpec {
        name: "comm".to_owned(),
        fine_b_vars: vec!["fx".to_owned(), "fy".to_owned()],
        fine_q: vec![PolyExpr::param("x"), PolyExpr::param("y")],
        coarsen_r: vec![PolyExpr::sum(PolyExpr::param("fx"), PolyExpr::param("fy"))],
        provenance: Provenance::default(),
    });
    let t_fine = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "scheme_fine".to_owned(),
        family: fp_nc_fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![q(1)],
        designated_candidate: Some(CandidateSelector::ById("c1".to_owned())),
        check_universal_ring: false,
        fine_base_value: Some(vec![q(1), q(0)]),
        provenance: Provenance::default(),
    })
    .unwrap();
    let o_fine = solve_robustness_task(&t_fine);
    assert_eq!(o_fine.verdict, Verdict::Refuted);
    let rc = o_fine.robustness.unwrap().reading_comparison.unwrap();
    assert!(rc.commutativity_verified);
    assert!(!rc.coarse_robust);
    assert!(rc.fine_robust);
    assert!(rc.coarse_implies_fine_preserved);
}

#[test]
fn p7_illegal_execution_and_minor_applicability_and_ac6_silences() {
    // 1. P7 raw_sequence with violated Busy StateLaw -> legal_execution_exists == Some(false)
    let pres_illegal = Presentation {
        name: "M_illegal".to_owned(),
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
                state_laws: vec![StateLaw {
                    name: "busy_req".to_owned(),
                    kind: LawKind::Representation,
                    polynomial: PolyExpr::diff(PolyExpr::state("B"), PolyExpr::rat(1, 1).unwrap()),
                    provenance: None,
                }],
                provenance: None,
            },
        ],
        operations: vec![OperationDecl {
            name: "begin".to_owned(),
            source_phase: "Idle".to_owned(),
            target_phase: "Busy".to_owned(),
            args: vec![],
            domain_laws: vec![],
            updates: BTreeMap::from([("B".to_owned(), PolyExpr::state("B"))]),
            provenance: None,
        }],
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
    let p7_fam = FamilySpec {
        name: "P7Illegal".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["u".to_owned()],
            b_vars: vec!["b".to_owned()],
            reading_q: vec![PolyExpr::param("u")],
            space: RealizationSpace::FiniteMembers(vec![RealizationMember {
                id: "u_bad".to_owned(),
                assignments: BTreeMap::from([("u".to_owned(), CoordValue::Observed(q(0)))]),
                is_raw_candidate: true,
                presentation: Some(pres_illegal),
                origin: src("u-bad", OriginKind::LlmCandidate),
            }]),
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec!["c".to_owned()],
            pi: vec![PolyExpr::param("c")],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".to_owned(),
                assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(0)))]),
                origin: src("c0", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![],
            invertibles: vec![],
            preservation: None,
            raw_sequence: Some(RawSequenceCheck {
                start_phase: "Idle".to_owned(),
                start_state: BTreeMap::from([("B".to_owned(), q(0))]),
                steps: vec![("begin".to_owned(), vec![])],
                observation_name: "read".to_owned(),
                baseline_step_index: None,
                provenance: Provenance::default(),
            }),
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };
    let p7_t = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "p7_illegal".to_owned(),
        family: p7_fam.clone(),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![q(0)],
        designated_candidate: Some(CandidateSelector::ById("c0".to_owned())),
        check_universal_ring: false,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    let p7_out = solve_robustness_task(&p7_t);
    assert_eq!(p7_out.verdict, Verdict::Refuted);
    let ce = p7_out
        .robustness
        .unwrap()
        .valid_designated
        .unwrap()
        .counterexample
        .unwrap();
    assert!(!ce.passed);
    assert_eq!(ce.legal_execution_exists, Some(false));
    assert!(
        ce.residuals
            .iter()
            .any(|r| r.contains("Busy.busy_req = -1"))
    );

    // 2. Minor #2: ByValues not matching FiniteMembers candidate -> Undetermined(ApplicabilityConditionNotMet)
    let by_val_t = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "by_val_miss".to_owned(),
        family: p7_fam.clone(),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![q(0)],
        designated_candidate: Some(CandidateSelector::ByValues(BTreeMap::from([(
            "c".to_owned(),
            q(99),
        )]))),
        check_universal_ring: false,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    assert!(matches!(
        solve_robustness_task(&by_val_t).verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { .. })
    ));

    // 3. M7: sort.rank == 2 -> Undetermined(ApplicabilityConditionNotMet)
    let mut rank2_fam = p7_fam;
    if let RealizationSpace::FiniteMembers(ref mut ms) = rank2_fam.realizations.space {
        ms[0].presentation.as_mut().unwrap().sorts[0].rank = 2;
    }
    let r2_t = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "rank2".to_owned(),
        family: rank2_fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: vec![q(0)],
        designated_candidate: None,
        check_universal_ring: false,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    assert!(matches!(
        solve_robustness_task(&r2_t).verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { .. })
    ));

    // 4. AC6: UniversalRingOutOfScope for CoeffDomain::Z and Fp enum limit exceeded
    let z_ur_fam = FamilySpec {
        name: "ZUr".to_owned(),
        coeff_domain: CoeffDomain::Z,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["u".to_owned()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::FiniteMembers(vec![RealizationMember {
                id: "u0".to_owned(),
                assignments: BTreeMap::from([("u".to_owned(), CoordValue::Observed(z(0)))]),
                is_raw_candidate: false,
                presentation: None,
                origin: src("z-u0", OriginKind::StaticAnalysis),
            }]),
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec!["c".to_owned()],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".to_owned(),
                assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(z(0)))]),
                origin: src("z-c0", OriginKind::HumanAdopted),
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
    let z_ur_t = CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: "z_ur".to_owned(),
        family: z_ur_fam,
        point_domain: PointDomain::IntegerPoints,
        base_value: vec![],
        designated_candidate: Some(CandidateSelector::ById("c0".to_owned())),
        check_universal_ring: true,
        fine_base_value: None,
        provenance: Provenance::default(),
    })
    .unwrap();
    assert!(matches!(
        solve_robustness_task(&z_ur_t).verdict,
        Verdict::Undetermined(SilenceReason::UniversalRingOutOfScope { .. })
    ));
}
