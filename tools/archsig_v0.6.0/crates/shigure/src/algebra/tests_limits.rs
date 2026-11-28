//! AC1 リソース暴走ガード（`BigInt` bit 長上限・多項式項数上限・`ShigureLimits` 伝播）の単体テスト。

use crate::algebra::MonomialOrder;
use crate::algebra::groebner::GroebnerBasis;
use crate::algebra::linear::smith_normal_form_z_with_limits;
use crate::algebra::poly::{AlgebraError, Poly, VarOrder};
use crate::algebra::scalar::Rat;
use crate::algebra::snf::{SnfFactorizationQ, SnfFactorizationZ};
use crate::algebra::syzygy::compute_syzygies_field_with_limits;
use crate::ir::change::{ChangeSpec, EditableTarget, FixedTarget, ParamDecl};
use crate::ir::presentation::{
    ComparisonPair, CoordDecl, ObservationDecl, OperationDecl, PhaseDecl, Presentation, SortDecl,
    StateComparison, TranslatedStep, TranslatedWord, WordTranslation,
};
use crate::ir::provenance::{OriginKind, Provenance, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::ir::validate::CheckedShigureTask;
use crate::limits::{ShigureLimits, active_limits, with_active_limits};
use crate::solver::{ShigureQueryKind, execute_shigure_task};
use num_bigint::BigInt;
use std::collections::BTreeMap;

#[test]
fn groebner_enforces_bigint_bit_limit_without_false_verdict() {
    let vars = VarOrder::new(vec!["x".into(), "y".into()]).unwrap();
    let x = Poly::var(2, 0, Rat::zero());
    let y = Poly::var(2, 1, Rat::zero());
    // x - 256 (9 bit) と x^2 - y の簡約で 256^2 = 65536 (17 bit) が生成される。
    let f1 = x.sub(&Poly::constant(2, Rat::from_int(256)));
    let f2 = x.mul(&x).sub(&y);

    let limits = ShigureLimits {
        max_bigint_bits: 12,
        ..Default::default()
    };

    let err = GroebnerBasis::compute_with_limits(&[f1, f2], vars, MonomialOrder::Grevlex, &limits)
        .expect_err("17-bit coefficient must trip 12-bit limit");
    match &err {
        AlgebraError::ResourceLimitExceeded {
            limit_name,
            limit,
            observed,
            ..
        } => {
            assert_eq!(limit_name, "max_bigint_bits");
            assert_eq!(*limit, 12);
            assert!(*observed > 12);
        }
        other => panic!("expected ResourceLimitExceeded, got {other:?}"),
    }

    let silence = SilenceReason::from_algebra_with(err, |_| unreachable!("must map directly"));
    assert_eq!(silence.code(), "resource_limit_exceeded");
    let json = silence.to_json().canonical();
    assert!(json.contains("\"code\":\"resource_limit_exceeded\""));
    assert!(json.contains("\"limit_name\":\"max_bigint_bits\""));
    assert!(matches!(
        Verdict::Undetermined(silence),
        Verdict::Undetermined(..)
    ));
}

#[test]
fn groebner_and_syzygy_enforce_poly_term_limit() {
    let vars = VarOrder::new(vec!["x".into(), "y".into(), "z".into()]).unwrap();
    let x = Poly::var(3, 0, Rat::zero());
    let y = Poly::var(3, 1, Rat::zero());
    let z = Poly::var(3, 2, Rat::zero());
    let one = Poly::constant(3, Rat::from_int(1));

    // f1 = x - (y + 1)^2 (4 項), f2 = x^2 - z (2 項)
    // S 多項式 / 簡約で (y + 1)^4 - z (6 項) が現れ、上限 5 を超える。
    let y_plus_1 = y.add(&one);
    let f1 = x.sub(&y_plus_1.mul(&y_plus_1));
    let f2 = x.mul(&x).sub(&z);

    let limits = ShigureLimits {
        max_poly_terms: 5,
        ..Default::default()
    };

    let gb_err =
        GroebnerBasis::compute_with_limits(&[f1, f2], vars.clone(), MonomialOrder::Lex, &limits)
            .expect_err("expanded polynomial term count must trip max_poly_terms=5");
    assert!(matches!(
        gb_err,
        AlgebraError::ResourceLimitExceeded {
            ref limit_name,
            limit: 5,
            observed,
            ..
        } if limit_name == "max_poly_terms" && observed > 5
    ));

    // syzygy 側でも同じ項数上限を検出する。
    let syz_limits = ShigureLimits {
        max_poly_terms: 4,
        ..Default::default()
    };
    let g1 = x.sub(&y.add(&one));
    let g2 = y_plus_1.mul(&y_plus_1).sub(&z);
    let g3 = x.mul(&x).sub(&z);
    let syz_err =
        compute_syzygies_field_with_limits(&[g1, g2, g3], vars, MonomialOrder::Lex, &syz_limits)
            .expect_err("syzygy computation must enforce max_poly_terms=4");
    assert!(matches!(
        syz_err,
        AlgebraError::ResourceLimitExceeded {
            ref limit_name,
            limit: 4,
            observed,
            ..
        } if limit_name == "max_poly_terms" && observed > 4
    ));
}

#[test]
fn snf_z_and_q_enforce_bigint_bit_limit() {
    let mat_z = vec![
        vec![BigInt::from(17), BigInt::from(19)],
        vec![BigInt::from(23), BigInt::from(29)],
    ];
    let limits = ShigureLimits {
        max_bigint_bits: 5,
        ..Default::default()
    };

    let err_lin = smith_normal_form_z_with_limits(&mat_z, 2, &limits)
        .expect_err("smith_normal_form_z must trip 5-bit limit");
    assert!(matches!(
        err_lin,
        AlgebraError::ResourceLimitExceeded {
            ref limit_name,
            limit: 5,
            ..
        } if limit_name == "max_bigint_bits"
    ));

    let err_snf_z = SnfFactorizationZ::compute_with_limits(&mat_z, 2, &limits)
        .expect_err("SnfFactorizationZ must trip 5-bit limit");
    assert!(matches!(
        err_snf_z,
        AlgebraError::ResourceLimitExceeded {
            ref limit_name,
            limit: 5,
            ..
        } if limit_name == "max_bigint_bits"
    ));

    let mat_q = vec![
        vec![Rat::from_int(17), Rat::from_int(19)],
        vec![Rat::from_int(23), Rat::from_int(29)],
    ];
    let err_snf_q = SnfFactorizationQ::compute_with_limits(&mat_q, 2, &limits)
        .expect_err("SnfFactorizationQ must trip 5-bit limit");
    assert!(matches!(
        err_snf_q,
        AlgebraError::ResourceLimitExceeded {
            ref limit_name,
            limit: 5,
            ..
        } if limit_name == "max_bigint_bits"
    ));
}

#[test]
fn with_active_limits_scopes_solver_to_undetermined_resource_limit() {
    let origin = SourceRef::new("test:origin", OriginKind::HumanAdopted);
    let before = Presentation {
        name: "Before".to_owned(),
        coeff_domain: CoeffDomain::Q,
        sorts: vec![SortDecl {
            name: "D".to_owned(),
            rank: 1,
            coeff_domain: CoeffDomain::Q,
            provenance: Some(origin.clone()),
        }],
        phases: vec![PhaseDecl {
            name: "S".to_owned(),
            coords: vec![CoordDecl::symbolic("x", "D")],
            state_laws: vec![],
            provenance: Some(origin.clone()),
        }],
        operations: vec![OperationDecl {
            name: "step".to_owned(),
            source_phase: "S".to_owned(),
            target_phase: "S".to_owned(),
            args: vec![("u".to_owned(), "D".to_owned())],
            domain_laws: vec![],
            updates: BTreeMap::from([("x".to_owned(), PolyExpr::state("x") + PolyExpr::arg("u"))]),
            provenance: Some(origin.clone()),
        }],
        observations: vec![ObservationDecl {
            name: "read".to_owned(),
            phase: "S".to_owned(),
            components: vec![PolyExpr::state("x")],
            provenance: Some(origin.clone()),
        }],
        provenance: Provenance::new(vec![origin.clone()], vec![]),
    };
    let after = Presentation {
        name: "After".to_owned(),
        coeff_domain: CoeffDomain::Q,
        sorts: before.sorts.clone(),
        phases: vec![PhaseDecl {
            name: "S".to_owned(),
            coords: vec![CoordDecl::symbolic("y", "D")],
            state_laws: vec![],
            provenance: None,
        }],
        operations: vec![OperationDecl {
            name: "step".to_owned(),
            source_phase: "S".to_owned(),
            target_phase: "S".to_owned(),
            args: vec![("u".to_owned(), "D".to_owned())],
            domain_laws: vec![],
            updates: BTreeMap::from([(
                "y".to_owned(),
                PolyExpr::state("y") + PolyExpr::param("p") * PolyExpr::arg("u"),
            )]),
            provenance: Some(origin.clone()),
        }],
        observations: vec![ObservationDecl {
            name: "read".to_owned(),
            phase: "S".to_owned(),
            components: vec![PolyExpr::param("q") * PolyExpr::state("y")],
            provenance: None,
        }],
        provenance: Provenance::new(vec![origin.clone()], vec![]),
    };
    let pair = ComparisonPair {
        before,
        after,
        state_comparisons: vec![StateComparison {
            after_phase: "S".to_owned(),
            before_phase: "S".to_owned(),
            map: BTreeMap::from([("x".to_owned(), PolyExpr::param("q") * PolyExpr::state("y"))]),
            provenance: None,
        }],
        word_translation: WordTranslation {
            entries: vec![TranslatedWord {
                after_operation: "step".to_owned(),
                steps: vec![TranslatedStep {
                    before_operation: "step".to_owned(),
                    arg_exprs: vec![PolyExpr::arg("u")],
                }],
                provenance: None,
            }],
        },
    };
    let change_spec = ChangeSpec {
        name: "H".to_owned(),
        coeff_domain: CoeffDomain::Q,
        parameters: ["p", "q"]
            .into_iter()
            .map(|n| ParamDecl {
                name: n.to_owned(),
                coeff_domain: CoeffDomain::Q,
                provenance: None,
            })
            .collect(),
        fixed: vec![FixedTarget::ObservationExpr {
            presentation: "Before".to_owned(),
            phase: "S".to_owned(),
            observation: "read".to_owned(),
        }],
        editable: vec![
            EditableTarget::OperationExpr {
                presentation: "After".to_owned(),
                operation: "step".to_owned(),
            },
            EditableTarget::StateComparisonExpr {
                after_phase: "S".to_owned(),
            },
        ],
        provenance: Provenance::new(vec![origin], vec![]),
    };
    let task = CheckedShigureTask::validate(pair, change_spec, None).unwrap();

    let before_limits = active_limits();
    let strict = ShigureLimits {
        max_poly_terms: 1,
        ..Default::default()
    };
    let outcome = with_active_limits(&strict, || {
        execute_shigure_task(&task, ShigureQueryKind::ConditionalSolutionSpace)
    });
    assert_eq!(active_limits(), before_limits);
    match outcome.verdict {
        Verdict::Undetermined(SilenceReason::ResourceLimitExceeded {
            limit_name, limit, ..
        }) => {
            assert_eq!(limit_name, "max_poly_terms");
            assert_eq!(limit, 1);
        }
        other => panic!("expected ResourceLimitExceeded, got {other:?}"),
    }
}
