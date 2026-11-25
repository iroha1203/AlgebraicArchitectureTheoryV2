//! Step 2 `solver/artin` 単体・パラメトリック・沈黙テスト（G-141 F1–F9・H4–H7・H10 / AC4・AC7）。

use crate::ir::artin::{
    ArtinTaskSpec, AuxiliaryDefSpec, BaseChangeSpec, CompositeStageSpec, validate_artin_task,
};
use crate::ir::change::NamedPoly;
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::solver::solve_artin_task;
use num_bigint::{BigInt, BigUint};

fn prov(clauses: Vec<MathClause>) -> Provenance {
    Provenance::new(
        vec![SourceRef::new("test:artin", OriginKind::HumanAdopted)],
        clauses,
    )
}

fn sv(name: &str) -> PolyExpr {
    PolyExpr::StateVar(name.into())
}

fn cz(n: i64) -> PolyExpr {
    PolyExpr::Const(ScalarLit::Z(BigInt::from(n)))
}

fn add(a: PolyExpr, b: PolyExpr) -> PolyExpr {
    PolyExpr::Add(Box::new(a), Box::new(b))
}

fn sub(a: PolyExpr, b: PolyExpr) -> PolyExpr {
    PolyExpr::Sub(Box::new(a), Box::new(b))
}

fn mul(a: PolyExpr, b: PolyExpr) -> PolyExpr {
    PolyExpr::Mul(Box::new(a), Box::new(b))
}

fn pow(a: PolyExpr, e: u32) -> PolyExpr {
    PolyExpr::Pow(Box::new(a), e)
}

fn np(name: &str, expr: PolyExpr) -> NamedPoly {
    NamedPoly {
        name: name.into(),
        expr,
        provenance: None,
    }
}

#[test]
fn artin_h4_universal_first_obstruction_and_f4_nu1_vs_nu_ge_2() {
    // H4: Y = T^2, Y = 0 over Q => ν = 2, D = 2, κ_u != 0, constant_lift_exists = false
    let task_h4 = validate_artin_task(ArtinTaskSpec {
        name: "h4_t2".into(),
        coeff_domain: CoeffDomain::Q,
        obs_vars: vec!["T".into()],
        obs_relations: vec![],
        aux_defs: vec![AuxiliaryDefSpec {
            name: "Y".into(),
            expr: pow(sv("T"), 2),
        }],
        extra_laws: vec![np("y_zero", sv("Y"))],
        base_point: vec![("T".into(), cz(0))],
        max_order: 4,
        max_artin_dim: None,
        composite_stage: None,
        base_change: None,
        non_noetherian_infinite: false,
        provenance: prov(vec![MathClause::G141F1, MathClause::G141F4]),
    })
    .unwrap();
    let out_h4 = solve_artin_task(&task_h4);
    assert_eq!(out_h4.verdict, Verdict::Refuted);
    let d4 = out_h4.artin.unwrap();
    assert_eq!(d4.test_ring_family, "all_local_artin_algebras_universal_quotient");
    assert!(d4.is_free_observation_chart);
    assert_eq!(d4.syntactic_degree_bound, Some(2));
    assert_eq!(d4.detection_order_nu, Some(2));
    assert!(!d4.local_isomorphism_at_base);
    assert_eq!(d4.lift_failure_mode, "nu_ge_2_realization_unliftable");
    let u4 = d4.universal_first_obstruction.unwrap();
    assert_eq!(u4.nu, 2);
    assert_eq!(u4.r_base_label, "A/m^2");
    assert_eq!(u4.r_prime_label, "A/m^3");
    assert!(u4.kappa_u_nonzero && u4.two_context_cech_matches);
    assert!(!u4.constant_lift_exists);

    // F4 対照: ν = 1（Y = T, Y = 0）=> 定値 lift 存在、指定観測方向のみ失敗
    let task_nu1 = validate_artin_task(ArtinTaskSpec {
        name: "f4_nu1".into(),
        coeff_domain: CoeffDomain::Q,
        obs_vars: vec!["T".into()],
        obs_relations: vec![],
        aux_defs: vec![AuxiliaryDefSpec {
            name: "Y".into(),
            expr: sv("T"),
        }],
        extra_laws: vec![np("y_zero", sv("Y"))],
        base_point: vec![("T".into(), cz(0))],
        max_order: 4,
        max_artin_dim: None,
        composite_stage: None,
        base_change: None,
        non_noetherian_infinite: false,
        provenance: prov(vec![MathClause::G141F4]),
    })
    .unwrap();
    let d1 = solve_artin_task(&task_nu1).artin.unwrap();
    assert_eq!(d1.detection_order_nu, Some(1));
    assert_eq!(
        d1.lift_failure_mode,
        "nu_eq_1_designated_direction_only_constant_lift_exists"
    );
    assert!(d1.universal_first_obstruction.unwrap().constant_lift_exists);
}

#[test]
fn artin_h5_chain_sharpness_and_non_free_chart_bound_omission() {
    // H5 自由観測 chart 連鎖 N = 1, 2, 3: Y_1 = T^2, ..., Y_N = Y_{N-1}^2, Y_N = 0 => ν = D = 2^N
    for n in 1..=3usize {
        let mut aux_defs = Vec::new();
        for j in 1..=n {
            let prev = if j == 1 {
                "T".to_owned()
            } else {
                format!("Y{}", j - 1)
            };
            aux_defs.push(AuxiliaryDefSpec {
                name: format!("Y{j}"),
                expr: pow(sv(&prev), 2),
            });
        }
        let expected = 1usize << n;
        let task = validate_artin_task(ArtinTaskSpec {
            name: format!("h5_chain_{n}"),
            coeff_domain: CoeffDomain::Q,
            obs_vars: vec!["T".into()],
            obs_relations: vec![],
            aux_defs,
            extra_laws: vec![np("yn_zero", sv(&format!("Y{n}")))],
            base_point: vec![("T".into(), cz(0))],
            max_order: expected + 1,
            max_artin_dim: None,
            composite_stage: None,
            base_change: None,
            non_noetherian_infinite: false,
            provenance: prov(vec![MathClause::G141F7]),
        })
        .unwrap();
        let d = solve_artin_task(&task).artin.unwrap();
        assert!(d.is_free_observation_chart);
        assert_eq!(d.detection_order_nu, Some(expected));
        assert_eq!(d.syntactic_degree_bound, Some(expected as u64));
    }

    // H5 非自由観測 chart: 既存関係 Y - T^N = 0 付きの Y = 0 => ν = N だが自由上界は適用しない (None)
    for n in [3u32, 4] {
        let task_rel = validate_artin_task(ArtinTaskSpec {
            name: format!("h5_non_free_n{n}"),
            coeff_domain: CoeffDomain::Q,
            obs_vars: vec!["T".into(), "Y".into()],
            obs_relations: vec![np("rel_yn", sub(sv("Y"), pow(sv("T"), n)))],
            aux_defs: vec![],
            extra_laws: vec![np("y_zero", sv("Y"))],
            base_point: vec![("T".into(), cz(0)), ("Y".into(), cz(0))],
            max_order: (n as usize) + 1,
            max_artin_dim: None,
            composite_stage: None,
            base_change: None,
            non_noetherian_infinite: false,
            provenance: prov(vec![MathClause::G141F7]),
        })
        .unwrap();
        let d = solve_artin_task(&task_rel).artin.unwrap();
        assert!(!d.is_free_observation_chart);
        assert_eq!(d.syntactic_degree_bound, None);
        assert_eq!(d.detection_order_nu, Some(n as usize));
    }
}

#[test]
fn artin_h10_snapshot_order_two_and_axis_local_iso() {
    // H10: E = mu * delta, E = 0 over Q => ν = 2, D = 2
    let task = validate_artin_task(ArtinTaskSpec {
        name: "h10_artin".into(),
        coeff_domain: CoeffDomain::Q,
        obs_vars: vec!["delta".into(), "mu".into()],
        obs_relations: vec![],
        aux_defs: vec![AuxiliaryDefSpec {
            name: "E".into(),
            expr: mul(sv("mu"), sv("delta")),
        }],
        extra_laws: vec![np("e_zero", sv("E"))],
        base_point: vec![("delta".into(), cz(0)), ("mu".into(), cz(0))],
        max_order: 4,
        max_artin_dim: None,
        composite_stage: None,
        base_change: None,
        non_noetherian_infinite: false,
        provenance: prov(vec![MathClause::G141F2, MathClause::G141F4]),
    })
    .unwrap();
    let d = solve_artin_task(&task).artin.unwrap();
    assert_eq!(d.detection_order_nu, Some(2));
    assert_eq!(d.syntactic_degree_bound, Some(2));

    // 軸制限 μ = 0 上では E = μδ ≡ 0 のため全次数 lift（ν = ∞, Established）
    let task_axis = validate_artin_task(ArtinTaskSpec {
        name: "h10_axis_mu_zero".into(),
        coeff_domain: CoeffDomain::Q,
        obs_vars: vec!["delta".into(), "mu".into()],
        obs_relations: vec![np("mu_zero", sv("mu"))],
        aux_defs: vec![AuxiliaryDefSpec {
            name: "E".into(),
            expr: mul(sv("mu"), sv("delta")),
        }],
        extra_laws: vec![np("e_zero", sv("E"))],
        base_point: vec![("delta".into(), cz(0)), ("mu".into(), cz(0))],
        max_order: 4,
        max_artin_dim: None,
        composite_stage: None,
        base_change: None,
        non_noetherian_infinite: false,
        provenance: prov(vec![MathClause::G141F3]),
    })
    .unwrap();
    let out_axis = solve_artin_task(&task_axis);
    assert_eq!(out_axis.verdict, Verdict::Established);
    let da = out_axis.artin.unwrap();
    assert_eq!(da.detection_order_nu, None);
    assert!(da.local_isomorphism_at_base);
    assert_eq!(da.lift_failure_mode, "infinite_local_iso");
}

#[test]
fn artin_f6_composition_min_law_parametric() {
    // (deg_u, deg_v) => ν(v ∘ u) = min(ν(u), ν(v))
    for (du, dv) in [(2u32, 3u32), (4u32, 2u32)] {
        let task = validate_artin_task(ArtinTaskSpec {
            name: format!("f6_comp_{du}_{dv}"),
            coeff_domain: CoeffDomain::Q,
            obs_vars: vec!["t".into(), "s".into()],
            obs_relations: vec![],
            aux_defs: vec![AuxiliaryDefSpec {
                name: "u_aux".into(),
                expr: pow(sv("t"), du),
            }],
            extra_laws: vec![np("u_law", sv("u_aux"))],
            base_point: vec![("t".into(), cz(0)), ("s".into(), cz(0))],
            max_order: 6,
            max_artin_dim: None,
            composite_stage: Some(CompositeStageSpec {
                aux_defs: vec![AuxiliaryDefSpec {
                    name: "v_aux".into(),
                    expr: pow(sv("s"), dv),
                }],
                extra_laws: vec![np("v_law", sv("v_aux"))],
            }),
            base_change: None,
            non_noetherian_infinite: false,
            provenance: prov(vec![MathClause::G141F6]),
        })
        .unwrap();
        let comp = solve_artin_task(&task).artin.unwrap().composition_law.unwrap();
        assert_eq!(comp.nu_u, Some(du as usize));
        assert_eq!(comp.nu_v, Some(dv as usize));
        assert_eq!(comp.nu_vu, Some((du.min(dv)) as usize));
        assert!(comp.min_law_verified);
    }

    // u が恒等 (extra_laws = [])、v が 3 次 => min(∞, 3) = 3
    let task_inf = validate_artin_task(ArtinTaskSpec {
        name: "f6_comp_inf_3".into(),
        coeff_domain: CoeffDomain::Q,
        obs_vars: vec!["t".into()],
        obs_relations: vec![],
        aux_defs: vec![],
        extra_laws: vec![],
        base_point: vec![("t".into(), cz(0))],
        max_order: 5,
        max_artin_dim: None,
        composite_stage: Some(CompositeStageSpec {
            aux_defs: vec![],
            extra_laws: vec![np("t3", pow(sv("t"), 3))],
        }),
        base_change: None,
        non_noetherian_infinite: false,
        provenance: prov(vec![MathClause::G141F6]),
    })
    .unwrap();
    let comp_inf = solve_artin_task(&task_inf)
        .artin
        .unwrap()
        .composition_law
        .unwrap();
    assert_eq!(comp_inf.nu_u, None);
    assert_eq!(comp_inf.nu_v, Some(3));
    assert_eq!(comp_inf.nu_vu, Some(3));
    assert!(comp_inf.min_law_verified);
}

#[test]
fn artin_h6_nilpotent_base_change_z_to_q_and_f2() {
    // H6: Z[t], J = (2*t^2 + t^3)
    let make_h6 = |target: CoeffDomain| {
        validate_artin_task(ArtinTaskSpec {
            name: "h6_z_base_change".into(),
            coeff_domain: CoeffDomain::Z,
            obs_vars: vec!["t".into()],
            obs_relations: vec![],
            aux_defs: vec![],
            extra_laws: vec![np("j_gen", add(mul(cz(2), pow(sv("t"), 2)), pow(sv("t"), 3)))],
            base_point: vec![("t".into(), cz(0))],
            max_order: 5,
            max_artin_dim: None,
            composite_stage: None,
            base_change: Some(BaseChangeSpec {
                target_domain: target,
                test_order: Some(2),
            }),
            non_noetherian_infinite: false,
            provenance: prov(vec![MathClause::G141F8]),
        })
        .unwrap()
    };

    // Z -> Q: ν_Z = 2, ν_Q = 2, flat = true, faithfully_flat = false, target_image != 0
    let bc_q = solve_artin_task(&make_h6(CoeffDomain::Q))
        .artin
        .unwrap()
        .base_change
        .unwrap();
    assert_eq!(bc_q.source_nu, Some(2));
    assert_eq!(bc_q.target_nu, Some(2));
    assert!(bc_q.flat_base_change && !bc_q.faithfully_flat);
    assert!(bc_q.abstract_tensor_nonzero && !bc_q.target_image_is_zero);

    // Z -> F_2: ν_Z = 2, ν_{F_2} = 3, D_2 = 2*Z*t^2 は抽象テンソル非零だが F_2[t]/(t^3) への像は 0
    let bc_f2 = solve_artin_task(&make_h6(CoeffDomain::Fp(BigUint::from(2u32))))
        .artin
        .unwrap()
        .base_change
        .unwrap();
    assert_eq!(bc_f2.source_nu, Some(2));
    assert_eq!(bc_f2.target_nu, Some(3));
    assert!(!bc_f2.flat_base_change && !bc_f2.faithfully_flat);
    assert!(bc_f2.abstract_tensor_nonzero);
    assert!(bc_f2.target_image_is_zero);
    assert!(bc_f2.target_image_generators.is_empty());
}

#[test]
fn artin_h7_non_noetherian_and_bounds_and_unobserved_silence() {
    // H7: 非 Noetherian 無限表示 T_i = T_{i+1}^2 相当入力 => NonNoetherianInfinitePresentation
    let task_h7 = validate_artin_task(ArtinTaskSpec {
        name: "h7_non_noetherian".into(),
        coeff_domain: CoeffDomain::Q,
        obs_vars: vec!["T0".into()],
        obs_relations: vec![],
        aux_defs: vec![],
        extra_laws: vec![],
        base_point: vec![("T0".into(), cz(0))],
        max_order: 4,
        max_artin_dim: None,
        composite_stage: None,
        base_change: None,
        non_noetherian_infinite: true,
        provenance: prov(vec![MathClause::G141F3]),
    })
    .unwrap();
    assert!(matches!(
        solve_artin_task(&task_h7).verdict,
        Verdict::Undetermined(SilenceReason::NonNoetherianInfinitePresentation { .. })
    ));

    // max_order = 2 に対し t^4 = 0 は上限内未検出のため ArtinOrderOutOfScope で沈黙（誤って local_iso にしない）
    let task_low_order = validate_artin_task(ArtinTaskSpec {
        name: "low_max_order".into(),
        coeff_domain: CoeffDomain::Q,
        obs_vars: vec!["t".into()],
        obs_relations: vec![],
        aux_defs: vec![],
        extra_laws: vec![np("t4", pow(sv("t"), 4))],
        base_point: vec![("t".into(), cz(0))],
        max_order: 2,
        max_artin_dim: None,
        composite_stage: None,
        base_change: None,
        non_noetherian_infinite: false,
        provenance: prov(vec![MathClause::G141F2]),
    })
    .unwrap();
    assert!(matches!(
        solve_artin_task(&task_low_order).verdict,
        Verdict::Undetermined(SilenceReason::ArtinOrderOutOfScope { .. })
    ));

    // max_artin_dim 超過 => ArtinOrderOutOfScope
    let task_low_dim = validate_artin_task(ArtinTaskSpec {
        name: "low_artin_dim".into(),
        coeff_domain: CoeffDomain::Q,
        obs_vars: vec!["x".into(), "y".into()],
        obs_relations: vec![],
        aux_defs: vec![],
        extra_laws: vec![np("x3", pow(sv("x"), 3))],
        base_point: vec![("x".into(), cz(0)), ("y".into(), cz(0))],
        max_order: 4,
        max_artin_dim: Some(2),
        composite_stage: None,
        base_change: None,
        non_noetherian_infinite: false,
        provenance: prov(vec![MathClause::G141F2]),
    })
    .unwrap();
    assert!(matches!(
        solve_artin_task(&task_low_dim).verdict,
        Verdict::Undetermined(SilenceReason::ArtinOrderOutOfScope { .. })
    ));

    // 未観測依存 => UnobservedDependency
    let task_unobs = validate_artin_task(ArtinTaskSpec {
        name: "unobs_artin".into(),
        coeff_domain: CoeffDomain::Q,
        obs_vars: vec!["t".into()],
        obs_relations: vec![],
        aux_defs: vec![],
        extra_laws: vec![np("t2", pow(sv("t"), 2))],
        base_point: vec![(
            "t".into(),
            PolyExpr::Unobserved {
                slot: "missing_t".into(),
                origin: None,
            },
        )],
        max_order: 3,
        max_artin_dim: None,
        composite_stage: None,
        base_change: None,
        non_noetherian_infinite: false,
        provenance: prov(vec![MathClause::G141F2]),
    })
    .unwrap();
    assert!(matches!(
        solve_artin_task(&task_unobs).verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { .. })
    ));
}

#[test]
fn artin_z_nonfree_sublattice_quotient_torsion_is_exact() {
    // ケース A: obs_relations = [2x], extra_laws = [x] => D_1 = (x)/(2x) ≅ Z/2Z
    let make_case = |extra: PolyExpr, target: CoeffDomain| {
        validate_artin_task(ArtinTaskSpec {
            name: "z_nonfree_torsion".into(),
            coeff_domain: CoeffDomain::Z,
            obs_vars: vec!["x".into()],
            obs_relations: vec![np("rel", mul(cz(2), sv("x")))],
            aux_defs: vec![],
            extra_laws: vec![np("extra", extra)],
            base_point: vec![("x".into(), cz(0))],
            max_order: 2,
            max_artin_dim: None,
            composite_stage: None,
            base_change: Some(BaseChangeSpec {
                target_domain: target,
                test_order: Some(1),
            }),
            non_noetherian_infinite: false,
            provenance: prov(vec![MathClause::G141F8]),
        })
        .unwrap()
    };

    // Z -> Q: (Z/2) ⊗ Q = 0
    let out_q = solve_artin_task(&make_case(sv("x"), CoeffDomain::Q));
    let bc_q = out_q.artin.as_ref().unwrap().base_change.as_ref().unwrap();
    assert!(!bc_q.abstract_tensor_nonzero);
    assert!(bc_q.target_image_is_zero);

    // Z -> F_2: (Z/2) ⊗ F_2 ≅ F_2 != 0
    let out_f2 = solve_artin_task(&make_case(sv("x"), CoeffDomain::Fp(2u32.into())));
    let bc_f2 = out_f2.artin.as_ref().unwrap().base_change.as_ref().unwrap();
    assert!(bc_f2.abstract_tensor_nonzero);
    assert!(!bc_f2.target_image_is_zero);

    // Z -> F_3: (Z/2) ⊗ F_3 = 0
    let out_f3 = solve_artin_task(&make_case(sv("x"), CoeffDomain::Fp(3u32.into())));
    let bc_f3 = out_f3.artin.as_ref().unwrap().base_change.as_ref().unwrap();
    assert!(!bc_f3.abstract_tensor_nonzero);
    assert!(bc_f3.target_image_is_zero);

    // ケース B: obs_relations = [2x], extra_laws = [2x] => D_1 = 0（snf_io の torsion=2 を誤継承しない）
    let out_zero = solve_artin_task(&make_case(
        mul(cz(2), sv("x")),
        CoeffDomain::Fp(2u32.into()),
    ));
    let bc_zero = out_zero
        .artin
        .as_ref()
        .unwrap()
        .base_change
        .as_ref()
        .unwrap();
    assert!(!bc_zero.abstract_tensor_nonzero);
    assert!(bc_zero.target_image_is_zero);
    assert!(bc_zero.source_dr_generators.is_empty());
    // F5: Z 上の冪零商は体上の局所 Artin 代数族と明示区別される
    assert_eq!(
        out_zero.artin.as_ref().unwrap().test_ring_family,
        "general_coeff_nilpotent_quotient"
    );
}

/// F2 回帰: Z 上 `composite_stage` で第 2 段 `extra_laws` が基点で零にならない場合、
/// 誤って `nu_v = 1` を返さず `ApplicabilityConditionNotMet` で沈黙すること。
#[test]
fn f2_artin_z_composite_stage_silences_on_nonvanishing_stage2_base_point() {
    let task = validate_artin_task(ArtinTaskSpec {
        name: "z_stage2_bad_base".into(),
        coeff_domain: CoeffDomain::Z,
        obs_vars: vec!["t".into()],
        obs_relations: vec![],
        aux_defs: vec![],
        extra_laws: vec![np("t2", pow(sv("t"), 2))],
        base_point: vec![("t".into(), cz(0))],
        max_order: 3,
        max_artin_dim: None,
        composite_stage: Some(CompositeStageSpec {
            aux_defs: vec![],
            extra_laws: vec![np("t_minus_1", sub(sv("t"), cz(1)))],
        }),
        base_change: None,
        non_noetherian_infinite: false,
        provenance: prov(vec![MathClause::G141F6]),
    })
    .unwrap();
    let out = solve_artin_task(&task);
    assert!(matches!(
        out.verdict,
        Verdict::Undetermined(SilenceReason::ApplicabilityConditionNotMet { .. })
    ));
}

/// F7 回帰: 空観測 chart（`obs_vars = []`, `extra_laws = []`）での体上 base_change が
/// 不要な `ArtinOrderOutOfScope` にならないこと。
#[test]
fn f7_artin_field_empty_chart_base_change_succeeds() {
    let task = validate_artin_task(ArtinTaskSpec {
        name: "empty_chart_bc".into(),
        coeff_domain: CoeffDomain::Q,
        obs_vars: vec![],
        obs_relations: vec![],
        aux_defs: vec![],
        extra_laws: vec![],
        base_point: vec![],
        max_order: 2,
        max_artin_dim: None,
        composite_stage: None,
        base_change: Some(BaseChangeSpec {
            target_domain: CoeffDomain::Q,
            test_order: Some(1),
        }),
        non_noetherian_infinite: false,
        provenance: prov(vec![MathClause::G141F8]),
    })
    .unwrap();
    let out = solve_artin_task(&task);
    assert_eq!(out.verdict, Verdict::Established);
    let bc = out.artin.as_ref().unwrap().base_change.as_ref().unwrap();
    assert!(bc.target_image_is_zero);
}
