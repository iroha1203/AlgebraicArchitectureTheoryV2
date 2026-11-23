//! `shigure_chevalley` ソルバの単体テスト（AC4・AC6・D6 射影・Chevalley 四分類・W5・W6）。

use crate::ir::change::{NamedPoly, PointDomain};
use crate::ir::family::{
    CandidateFamilySpec, CandidateMember, CandidateSpace, FamilySpec, GoodnessKind, GoodnessSpec,
    RealizationFamilySpec, RealizationSpace,
};
use crate::ir::presentation::CoordValue;
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::robustness::{
    CandidateSelector, CheckedChevalleyTask, ChevalleyTaskSpec, RationalFiberProbe,
};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::solver::solve_chevalley_task;
use std::collections::BTreeMap;

fn src(id: &str, kind: OriginKind) -> SourceRef {
    SourceRef::new(id, kind)
}

fn q(n: i64) -> ScalarLit {
    ScalarLit::rat(n, 1).expect("integer rational")
}

#[test]
fn chevalley_d6_hyperbola_existential_projection_exposes_open_locus_not_closure() {
    // Existential goodness: exists y such that x * y - 1 = 0 => image over u = x is D(x) (x invertible),
    // never closure A^1. At x = 0 fiber is empty; for all x != 0 fiber is non-empty.
    let fam = FamilySpec {
        name: "Hyperbola".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["x".to_owned()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: src("hyp-u", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec!["c".to_owned()],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c_any".to_owned(),
                assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(0)))]),
                origin: src("c-any", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Existential {
            witness_vars: vec!["y".to_owned()],
            equations: vec![NamedPoly::new(
                "hyp",
                PolyExpr::diff(
                    PolyExpr::prod(PolyExpr::param("x"), PolyExpr::param("y")),
                    PolyExpr::rat(1, 1).unwrap(),
                ),
            )],
            invertibles: vec![],
            preservation: None,
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };
    let task = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "chev_hyp".to_owned(),
        family: fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: None,
        designated_candidate: None,
        rational_fiber_probes: vec![],
        check_global_regular_section: false,
        check_universal_ring: false,
        provenance: Provenance::new(vec![], vec![MathClause::G141D6, MathClause::G141D7]),
    })
    .unwrap();

    let out = solve_chevalley_task(&task);
    // At x = 0, candidate c=0 fails; at x = 1, candidate c=0 passes -> mixed!
    assert_eq!(out.verdict, Verdict::Refuted);
    let det = out.chevalley.as_ref().expect("chevalley detail");
    assert_eq!(det.goodness_kind, GoodnessKind::Existential);
    let eff = det
        .effective_image_e
        .as_ref()
        .expect("existential effective image");
    assert!(!eff.is_empty);
    // Effective image E equals open locus D(x) (c = 0, x != 0), never A^1 closure.
    assert!(
        eff.strata
            .iter()
            .any(|(eqs, invs)| eqs == &vec!["c".to_owned()] && invs == &vec!["x".to_owned()]),
        "expected exact open stratum ([\"c\"], [\"x\"]), got {:?}",
        eff.strata
    );
    assert!(!det.mixed.is_empty);
    assert!(det.robust_all_pass.is_empty);
    assert!(det.all_fail.is_empty);
    assert!(det.empty_realizations.is_empty);
    let mw = det.mixed_witness_pair.as_ref().expect("mixed witness pair");
    assert!(mw.pass_witness.passed);
    assert_ne!(
        mw.pass_witness
            .realization
            .assignments
            .get("x")
            .map(String::as_str),
        Some("0")
    );
    assert!(!mw.fail_witness.passed);
    assert_eq!(
        mw.fail_witness
            .realization
            .assignments
            .get("x")
            .map(String::as_str),
        Some("0")
    );
}

#[test]
fn chevalley_four_regions_disjoint_and_exhaustive_with_all_four_populated() {
    // U has (u) and C has (c) with base reading q = c = 0 (Wait: take B empty so U varies independently, or u_vars = [u], c_vars = [c]):
    // To realize all 4 Chevalley regions simultaneously on a single family:
    // U constrained by c: let reading_q = [u * 0] ? Better: fiber relation via q(u) = c? Wait!
    // If q(u) = u * c - c? Look! Take U with unconstrained u in A^1, q(u) = (c_match) with:
    //   q(u) = (u) ... if pi(c) = c, then at each c: u = c (never empty).
    // Instead, realize 4 candidate classes via polynomial goodness & realization equations?
    // Wait: realizations U is a subspace of A^1(u) BEFORE intersecting with q(u) = pi(c)!
    // Wait: if q(u) = u^2 and pi(c) = c:
    //   Wait, over algebraic closure u^2 = c is non-empty for every c.
    // How can U_c be EMPTY over algebraic closure for some c?
    // When q(u) = u * 0 = 0 and pi(c) = c:
    //   For c != 0: q(u) = pi(c) gives 0 = c -> EMPTY realization fiber U_c!!
    //   Wait: at c = 0 only one candidate exists. How can BOTH c = 0..3 give 4 regions?
    // Easy!! Take B = [b], q(u) = u*(u - 1)*(u - 2), no wait: pi(c) = c * (c - 1) * (c - 2):
    // Even simpler: let q(u) = c? No, q only uses u! Take b = [b1, b2] or single q(u) = u * 0 + ... wait:
    // For FiniteMembers U = {0, 1, 2}: q(u) = u*(u-1)*(u-2) maps ALL of U to 0! Or take FiniteMembers C:
    // At c_empty = 9: pi(c_empty) = 9, while q(u) in {0, 1} (for FiniteMembers U = {u=0, u=1} with q(u) = u)!
    // WAIT: if C = {c_pass: 0, c_fail: 1, c_mixed: 2, c_empty: 9} with pi(c):
    //   Even with polynomial goodness:
    //   Take q(u) = u*(u - 1) ?? Wait: then q(0)=0, q(1)=0. Still need pi(c_empty) != 0!
    //   Wait: if U = {u=0, u=1, u=2}? If base_value = None, Chevalley pulls back along q(u) = pi(c)!
    //   Look how clean this is:
    //   Take U = A^1(u), C = FiniteMembers {c=0, c=1, c=2, c=3}, reading q(u) = 0? No: if q(u) = u, then U_c = {c} has only 1 u!
    //   Take q(u) = u^2 * (u - 1)^2? Wait: if q(u) = 0 for all U? Then for any c with pi(c) = 0, U_c = U, and for pi(c) = 1, U_c = empty!
    //   YES!! Look at that:
    //   Take U = {u in {0, 1}}, C = {c in {0, 1, 2, 3}}:
    //     reading_q = [u*(u-1)] = [0, 0] for both u=0 and u=1!
    //     pi(c) = [ (c - 0)*(c - 1)*(c - 2) ]  -> zero iff c in {0, 1, 2}, nonzero (= 6) at c = 3!
    //     So:
    //       - For c in {0, 1, 2}: U_c = {u=0, u=1} (two points!)
    //       - For c = 3: U_c = EMPTY -> c = 3 lies in `empty_realizations`!
    //     Now choose goodness equation on (u, c) = c*(c - 2*u) + (c - 1)*(c - 2) * ... wait:
    //       At c = 0: always pass -> goodness = 0 when c=0!
    //       At c = 1: always fail -> goodness != 0 for BOTH u=0, u=1!
    //       At c = 2: mixed -> passes u=0, fails u=1!
    //     Polynomial: E_ok(u, c):  c * ( (c - 2)*u + (c - 1) ) = 0?
    //       Check:
    //       - c = 0: 0 * (...) = 0 -> passes u=0 AND u=1! -> `robust_all_pass` = {0}
    //       - c = 1: 1 * ((-1)*u + 0) = -u -> wait: at u=0 gives 0! Need nonzero for u=0 and u=1!
    //         Take: c * (u*(c - 2) + (c - 1)*(c - 2) ... wait: at c=1, want nonzero for BOTH u=0 and u=1: just make it independent of u when c=1!
    //         Formula: `c * ((c - 1) * u + (c - 2))`:
    //         - c = 0: 0 = 0 (always passes!) -> `robust_all_pass`!
    //         - c = 1: 1 * (0*u - 1) = -1 != 0 for BOTH u=0 and u=1 -> `all_fail`!
    //         - c = 2: 2 * (1*u + 0) = 2*u -> at u=0 gives 0 (pass!), at u=1 gives 2 (fail!) -> `mixed`!
    //         - c = 3: U_3 is empty because pi(3) = 6 != 0 = q(u) -> `empty_realizations`!
    let u = PolyExpr::param("u");
    let c = PolyExpr::param("c");
    let fam = FamilySpec {
        name: "FourClasses".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["u".to_owned()],
            b_vars: vec!["b".to_owned()],
            reading_q: vec![PolyExpr::prod(
                u.clone(),
                PolyExpr::diff(u.clone(), PolyExpr::rat(1, 1).unwrap()),
            )],
            space: RealizationSpace::FiniteMembers(vec![
                crate::ir::family::RealizationMember {
                    id: "u0".to_owned(),
                    assignments: BTreeMap::from([("u".to_owned(), CoordValue::Observed(q(0)))]),
                    is_raw_candidate: false,
                    presentation: None,
                    origin: src("u0", OriginKind::StaticAnalysis),
                },
                crate::ir::family::RealizationMember {
                    id: "u1".to_owned(),
                    assignments: BTreeMap::from([("u".to_owned(), CoordValue::Observed(q(1)))]),
                    is_raw_candidate: false,
                    presentation: None,
                    origin: src("u1", OriginKind::StaticAnalysis),
                },
            ]),
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec!["c".to_owned()],
            pi: vec![PolyExpr::prod(
                PolyExpr::prod(
                    c.clone(),
                    PolyExpr::diff(c.clone(), PolyExpr::rat(1, 1).unwrap()),
                ),
                PolyExpr::diff(c.clone(), PolyExpr::rat(2, 1).unwrap()),
            )],
            space: CandidateSpace::FiniteMembers(vec![
                CandidateMember {
                    id: "c_pass".to_owned(),
                    assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(0)))]),
                    origin: src("c0", OriginKind::HumanAdopted),
                },
                CandidateMember {
                    id: "c_fail".to_owned(),
                    assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(1)))]),
                    origin: src("c1", OriginKind::HumanAdopted),
                },
                CandidateMember {
                    id: "c_mixed".to_owned(),
                    assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(2)))]),
                    origin: src("c2", OriginKind::HumanAdopted),
                },
                CandidateMember {
                    id: "c_empty".to_owned(),
                    assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(3)))]),
                    origin: src("c3", OriginKind::HumanAdopted),
                },
            ]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new(
                "partition_eq",
                PolyExpr::prod(
                    c.clone(),
                    PolyExpr::sum(
                        PolyExpr::prod(PolyExpr::diff(c.clone(), PolyExpr::rat(1, 1).unwrap()), u),
                        PolyExpr::diff(c, PolyExpr::rat(2, 1).unwrap()),
                    ),
                ),
            )],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };

    let task_pass = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "four_regions".to_owned(),
        family: fam.clone(),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: None,
        designated_candidate: Some(CandidateSelector::ById("c_pass".to_owned())),
        rational_fiber_probes: vec![],
        check_global_regular_section: false,
        check_universal_ring: false,
        provenance: Provenance::default(),
    })
    .unwrap();
    let out = solve_chevalley_task(&task_pass);
    assert_eq!(out.verdict, Verdict::Established);
    let det = out.chevalley.as_ref().expect("chevalley detail");
    assert_eq!(
        det.designated_candidate_class.as_deref(),
        Some("robust_all_pass")
    );
    assert!(!det.robust_all_pass.is_empty);
    assert!(!det.all_fail.is_empty);
    assert!(!det.mixed.is_empty);
    assert!(!det.empty_realizations.is_empty);

    // Mixed witness pair populated automatically from `mixed`
    let mw = det.mixed_witness_pair.as_ref().expect("mixed witness");
    assert!(mw.pass_witness.passed);
    assert!(!mw.fail_witness.passed);

    // Verify designated_candidate_class identifies each of the other 3 regions accurately & disjointly.
    for (cid, expected) in [
        ("c_fail", "all_fail"),
        ("c_mixed", "mixed"),
        ("c_empty", "empty_realizations"),
    ] {
        let t = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
            name: format!("check_{cid}"),
            family: fam.clone(),
            point_domain: PointDomain::AlgebraicClosure,
            base_value: None,
            designated_candidate: Some(CandidateSelector::ById(cid.to_owned())),
            rational_fiber_probes: vec![],
            check_global_regular_section: false,
            check_universal_ring: false,
            provenance: Provenance::default(),
        })
        .unwrap();
        let o = solve_chevalley_task(&t);
        assert_eq!(o.verdict, Verdict::Refuted);
        assert_eq!(
            o.chevalley.unwrap().designated_candidate_class.as_deref(),
            Some(expected)
        );
    }

    // Algebraic property assertion: constructible sets from `build_family_constructible_sets`
    // form a pairwise-disjoint full partition of C (tested on continuous polynomial scheme too).
    let raw_fam = FamilySpec {
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec!["c".to_owned()],
            pi: vec![PolyExpr::param("c")],
            space: CandidateSpace::PolynomialScheme {
                equations: vec![],
                invertibles: vec![],
                origin: src("c-scheme", OriginKind::StaticAnalysis),
            },
        },
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["u".to_owned()],
            b_vars: vec!["b".to_owned()],
            reading_q: vec![PolyExpr::rat(0, 1).unwrap()],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: src("u-scheme", OriginKind::StaticAnalysis),
            },
        },
        ..fam
    };
    let checked = crate::ir::family::CheckedFamilySpec::validate(raw_fam).unwrap();
    let sets = crate::solver::chevalley::build_family_constructible_sets(&checked, None).unwrap();
    let r = &sets.robust_all_pass;
    let f = &sets.all_fail;
    let m = &sets.mixed;
    let e = &sets.empty_realizations;
    assert!(r.intersect(f).unwrap().is_empty());
    assert!(r.intersect(m).unwrap().is_empty());
    assert!(r.intersect(e).unwrap().is_empty());
    assert!(f.intersect(m).unwrap().is_empty());
    assert!(f.intersect(e).unwrap().is_empty());
    assert!(m.intersect(e).unwrap().is_empty());
    let cov = r.union(f).unwrap().union(m).unwrap().union(e).unwrap();
    assert!(sets.c_space.difference(&cov).unwrap().is_empty());
    assert!(cov.difference(&sets.c_space).unwrap().is_empty());
}

#[test]
fn chevalley_w5_etale_cover_and_w6_geometric_vs_universal_ring_contrast() {
    // W5: z^2 = t on G_m (t invertible). Geometric E_exists is valid on ALL of G_m (kbar points),
    // yet at rational probe t = 2 over Q the fiber has NO Q-points, and global regular section over k[t, t^-1] fails!
    let t = PolyExpr::param("t");
    let z = PolyExpr::param("z");
    let w5_fam = FamilySpec {
        name: "W5Gm".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "Gm".to_owned(),
            u_vars: vec!["t".to_owned()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![],
                invertibles: vec![NamedPoly::new("t_unit", t.clone())],
                is_raw_candidate: false,
                origin: src("w5-gm", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec!["c".to_owned()],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".to_owned(),
                assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(0)))]),
                origin: src("w5-c0", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Existential {
            witness_vars: vec!["z".to_owned()],
            equations: vec![NamedPoly::new(
                "cover",
                PolyExpr::diff(PolyExpr::pow(z, 2), t),
            )],
            invertibles: vec![],
            preservation: None,
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };
    let w5_task = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "w5_chev".to_owned(),
        family: w5_fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: None,
        designated_candidate: None,
        rational_fiber_probes: vec![
            RationalFiberProbe {
                name: "t_eq_4".to_owned(),
                u_assignments: BTreeMap::from([("t".to_owned(), q(4))]),
                c_assignments: BTreeMap::from([("c".to_owned(), q(0))]),
            },
            RationalFiberProbe {
                name: "t_eq_2".to_owned(),
                u_assignments: BTreeMap::from([("t".to_owned(), q(2))]),
                c_assignments: BTreeMap::from([("c".to_owned(), q(0))]),
            },
        ],
        check_global_regular_section: true,
        check_universal_ring: false,
        provenance: Provenance::default(),
    })
    .unwrap();

    let w5_out = solve_chevalley_task(&w5_task);
    assert_eq!(w5_out.verdict, Verdict::Established);
    let w5_det = w5_out.chevalley.expect("W5 detail");
    assert!(!w5_det.robust_all_pass.is_empty);
    assert!(w5_det.all_fail.is_empty);
    assert!(w5_det.mixed.is_empty);
    assert_eq!(w5_det.rational_fiber_probes.len(), 2);
    assert_eq!(
        w5_det.rational_fiber_probes[0].verdict,
        Verdict::Established
    );
    let rw_4 = w5_det.rational_fiber_probes[0]
        .rational_witness
        .as_ref()
        .and_then(|m| m.get("z"))
        .map(String::as_str);
    assert!(matches!(rw_4, Some("2" | "-2")));
    assert_eq!(w5_det.rational_fiber_probes[1].verdict, Verdict::Refuted);
    assert!(
        w5_det.rational_fiber_probes[1]
            .detail
            .contains("Rational Root Theorem")
    );
    let gsec = w5_det
        .global_regular_section
        .expect("global regular section check");
    assert_eq!(gsec.exists, Some(false));
    assert!(
        gsec.obstruction_detail
            .as_deref()
            .unwrap_or("")
            .contains("2*n = 1")
    );

    // W6: nilpotent fiber (rho - 1)^2 = 0 with goodness rho - 1 = 0
    // Chevalley sees `robust_all_pass` over closed points (kbar), YET `universal_ring_contrast` is `stable == Some(false)`!
    let rho_m1 = PolyExpr::diff(PolyExpr::param("rho"), PolyExpr::rat(1, 1).unwrap());
    let w6_fam = FamilySpec {
        name: "W6Contrast".to_owned(),
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
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "c0".to_owned(),
                assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(0)))]),
                origin: src("w6-c0", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new("unipotent_trivial", rho_m1)],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };
    let w6_task = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "w6_chev".to_owned(),
        family: w6_fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: Some(vec![q(0)]),
        designated_candidate: Some(CandidateSelector::ById("c0".to_owned())),
        rational_fiber_probes: vec![],
        check_global_regular_section: false,
        check_universal_ring: true,
        provenance: Provenance::default(),
    })
    .unwrap();
    let w6_out = solve_chevalley_task(&w6_task);
    assert_eq!(w6_out.verdict, Verdict::Established);
    let w6_det = w6_out.chevalley.expect("W6 chevalley");
    assert_eq!(
        w6_det.designated_candidate_class.as_deref(),
        Some("robust_all_pass")
    );
    let uc = w6_det.universal_ring_contrast.expect("universal contrast");
    assert_eq!(uc.stable, Some(false));
    assert!(uc.dual_number_counterexample.is_some());
}

#[test]
fn chevalley_silences_on_unobserved_slot() {
    let fam = FamilySpec {
        name: "UnobsChev".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["u".to_owned()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::FiniteMembers(vec![crate::ir::family::RealizationMember {
                id: "u0".to_owned(),
                assignments: BTreeMap::from([("u".to_owned(), CoordValue::Missing)]),
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
                assignments: BTreeMap::from([("c".to_owned(), CoordValue::Observed(q(0)))]),
                origin: src("c0", OriginKind::HumanAdopted),
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
    let task = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "unobs".to_owned(),
        family: fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: None,
        designated_candidate: None,
        rational_fiber_probes: vec![],
        check_global_regular_section: false,
        check_universal_ring: false,
        provenance: Provenance::default(),
    })
    .unwrap();
    let out = solve_chevalley_task(&task);
    assert!(matches!(
        out.verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { .. })
    ));
}

#[test]
fn chevalley_m1_m2_m4_m7_review_regressions() {
    use crate::ir::family::{RawSequenceCheck, RealizationMember};
    use crate::ir::presentation::{
        CoordDecl, ObservationDecl, OperationDecl, PhaseDecl, Presentation, SortDecl,
    };

    // 1. M1 + W5 fixed candidate z0 on G_m:
    //    (a) probe outside G_m (t = 0 violates t invertible) must be Refuted, never Established (z=0)!
    //    (b) fixed candidate z0 = 2 on G_m is mixed (passes t=4, fails otherwise).
    //    (c) unconstrained 1D z != 0 probe chooses verified nonzero z (never "0").
    let t = PolyExpr::param("t");
    let z = PolyExpr::param("z");
    let w5_fixed_fam = FamilySpec {
        name: "W5Fixed".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "Gm".to_owned(),
            u_vars: vec!["t".to_owned()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![],
                invertibles: vec![NamedPoly::new("t_unit", t.clone())],
                is_raw_candidate: false,
                origin: src("w5-gm", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec!["z0".to_owned()],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![CandidateMember {
                id: "z_fixed".to_owned(),
                assignments: BTreeMap::from([("z0".to_owned(), CoordValue::Observed(q(2)))]),
                origin: src("z2", OriginKind::HumanAdopted),
            }]),
        },
        goodness: GoodnessSpec::Direct {
            equations: vec![NamedPoly::new(
                "cover_at_z0",
                PolyExpr::diff(PolyExpr::pow(PolyExpr::param("z0"), 2), t.clone()),
            )],
            invertibles: vec![],
            preservation: None,
            raw_sequence: None,
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };
    let t_w5_fix = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "w5_fixed".to_owned(),
        family: w5_fixed_fam.clone(),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: None,
        designated_candidate: Some(CandidateSelector::ById("z_fixed".to_owned())),
        rational_fiber_probes: vec![RationalFiberProbe {
            name: "outside_gm_t0".to_owned(),
            u_assignments: BTreeMap::from([("t".to_owned(), q(0))]),
            c_assignments: BTreeMap::new(),
        }],
        check_global_regular_section: true,
        check_universal_ring: false,
        provenance: Provenance::default(),
    })
    .unwrap();
    let o_w5_fix = solve_chevalley_task(&t_w5_fix);
    assert_eq!(o_w5_fix.verdict, Verdict::Refuted);
    let det_f = o_w5_fix.chevalley.unwrap();
    assert_eq!(det_f.designated_candidate_class.as_deref(), Some("mixed"));
    assert_eq!(det_f.rational_fiber_probes[0].verdict, Verdict::Refuted);

    // 2. M1 unconstrained 1D z != 0 probe must never return z = "0"
    let inv_only_fam = FamilySpec {
        name: "InvOnly1D".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["t".to_owned()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::PolynomialScheme {
                equations: vec![],
                invertibles: vec![],
                is_raw_candidate: false,
                origin: src("u", OriginKind::StaticAnalysis),
            },
        },
        candidates: CandidateFamilySpec {
            name: "C".to_owned(),
            c_vars: vec![],
            pi: vec![],
            space: CandidateSpace::FiniteMembers(vec![]),
        },
        goodness: GoodnessSpec::Existential {
            witness_vars: vec!["z".to_owned()],
            equations: vec![],
            invertibles: vec![NamedPoly::new("z_nz", z)],
            preservation: None,
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };
    let t_inv = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "inv1d".to_owned(),
        family: inv_only_fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: None,
        designated_candidate: None,
        rational_fiber_probes: vec![RationalFiberProbe {
            name: "p1".to_owned(),
            u_assignments: BTreeMap::from([("t".to_owned(), q(1))]),
            c_assignments: BTreeMap::new(),
        }],
        check_global_regular_section: false,
        check_universal_ring: false,
        provenance: Provenance::default(),
    })
    .unwrap();
    let o_inv = solve_chevalley_task(&t_inv);
    let p_res = &o_inv.chevalley.unwrap().rational_fiber_probes[0];
    assert_eq!(p_res.verdict, Verdict::Established);
    assert_ne!(
        p_res
            .rational_witness
            .as_ref()
            .and_then(|w| w.get("z"))
            .map(String::as_str),
        Some("0")
    );

    // 3. M2: Closed curve V(t - 4) where z^2 = t HAS section z = 2 must return exists: None (ApplicabilityConditionNotMet)
    let mut closed_v_fam = w5_fixed_fam;
    closed_v_fam.realizations.space = RealizationSpace::PolynomialScheme {
        equations: vec![NamedPoly::new(
            "t4",
            PolyExpr::diff(t, PolyExpr::rat(4, 1).unwrap()),
        )],
        invertibles: vec![],
        is_raw_candidate: false,
        origin: src("v4", OriginKind::StaticAnalysis),
    };
    let t_closed_v = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "m2_closed_v".to_owned(),
        family: closed_v_fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: None,
        designated_candidate: None,
        rational_fiber_probes: vec![],
        check_global_regular_section: true,
        check_universal_ring: false,
        provenance: Provenance::default(),
    })
    .unwrap();
    let gs_closed = solve_chevalley_task(&t_closed_v)
        .chevalley
        .unwrap()
        .global_regular_section
        .unwrap();
    assert_eq!(gs_closed.exists, None);
    assert!(matches!(
        gs_closed.silence_reason,
        Some(SilenceReason::ApplicabilityConditionNotMet { .. })
    ));

    // 4. M4(2) & M7: duplicate u coords on raw_sequence AND sort.rank = 2 both silence with ApplicabilityConditionNotMet
    let make_min_pres = |name: &str, rank: usize| Presentation {
        name: name.to_owned(),
        coeff_domain: CoeffDomain::Q,
        sorts: vec![SortDecl {
            name: "S".to_owned(),
            rank,
            coeff_domain: CoeffDomain::Q,
            provenance: None,
        }],
        phases: vec![PhaseDecl {
            name: "Idle".to_owned(),
            coords: vec![CoordDecl::symbolic("B", "S")],
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "nop".to_owned(),
            source_phase: "Idle".to_owned(),
            target_phase: "Idle".to_owned(),
            args: vec![],
            domain_laws: vec![],
            updates: BTreeMap::from([("B".to_owned(), PolyExpr::state("B"))]),
            provenance: None,
        }],
        observations: vec![ObservationDecl {
            name: "read".to_owned(),
            phase: "Idle".to_owned(),
            components: vec![PolyExpr::state("B")],
            provenance: None,
        }],
        provenance: Provenance::default(),
    };
    let dup_raw_fam = FamilySpec {
        name: "DupRaw".to_owned(),
        coeff_domain: CoeffDomain::Q,
        realizations: RealizationFamilySpec {
            name: "U".to_owned(),
            u_vars: vec!["u".to_owned()],
            b_vars: vec![],
            reading_q: vec![],
            space: RealizationSpace::FiniteMembers(vec![
                RealizationMember {
                    id: "u_a".to_owned(),
                    assignments: BTreeMap::from([("u".to_owned(), CoordValue::Observed(q(0)))]),
                    is_raw_candidate: false,
                    presentation: Some(make_min_pres("P1", 1)),
                    origin: src("ua", OriginKind::StaticAnalysis),
                },
                RealizationMember {
                    id: "u_b".to_owned(),
                    assignments: BTreeMap::from([("u".to_owned(), CoordValue::Observed(q(0)))]),
                    is_raw_candidate: true,
                    presentation: Some(make_min_pres("P2", 1)),
                    origin: src("ub", OriginKind::LlmCandidate),
                },
            ]),
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
            raw_sequence: Some(RawSequenceCheck {
                start_phase: "Idle".to_owned(),
                start_state: BTreeMap::from([("B".to_owned(), q(0))]),
                steps: vec![("nop".to_owned(), vec![])],
                observation_name: "read".to_owned(),
                baseline_step_index: None,
                provenance: Provenance::default(),
            }),
        },
        reading_comparison: None,
        provenance: Provenance::default(),
    };
    let t_dup = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "dup_raw".to_owned(),
        family: dup_raw_fam.clone(),
        point_domain: PointDomain::AlgebraicClosure,
        base_value: None,
        designated_candidate: None,
        rational_fiber_probes: vec![],
        check_global_regular_section: false,
        check_universal_ring: false,
        provenance: Provenance::default(),
    })
    .unwrap();
    assert!(matches!(
        solve_chevalley_task(&t_dup).verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { .. })
    ));

    let mut r2_fam = dup_raw_fam;
    if let RealizationSpace::FiniteMembers(ref mut ms) = r2_fam.realizations.space {
        ms.pop();
        ms[0].presentation = Some(make_min_pres("P_r2", 2));
    }
    let t_r2 = CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: "m7_rank2".to_owned(),
        family: r2_fam,
        point_domain: PointDomain::AlgebraicClosure,
        base_value: None,
        designated_candidate: None,
        rational_fiber_probes: vec![],
        check_global_regular_section: false,
        check_universal_ring: false,
        provenance: Provenance::default(),
    })
    .unwrap();
    assert!(matches!(
        solve_chevalley_task(&t_r2).verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { .. })
    ));
}
