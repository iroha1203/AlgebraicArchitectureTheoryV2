//! Phase 4 代数核（`syzygy`・`artin`・`cochain`・`poly` 偏微分/代入）の単体テスト（AC1）。

use crate::algebra::MonomialOrder;
use crate::algebra::artin::{
    DEFAULT_MAX_ARTIN_DIM, FiniteAlgebra, LocalArtinQuotient, SquareZeroExtension,
};
use crate::algebra::cochain::{CochainComplex, CochainMap};
use crate::algebra::poly::{AlgebraError, Monomial, Poly, VarOrder};
use crate::algebra::scalar::{FpElem, Rat};
use crate::algebra::syzygy::{
    DEFAULT_MAX_SYZYGY_PAIRS, compute_syzygies_field, compute_syzygies_z, jacobian_polys,
};
use num_bigint::{BigInt, BigUint};
use num_traits::{Signed, Zero};

fn var_q(n: usize, i: usize) -> Poly<Rat> {
    Poly::var(n, i, Rat::zero())
}

fn const_q(n: usize, v: i64) -> Poly<Rat> {
    Poly::constant(n, Rat::from_int(v))
}

#[test]
fn syzygy_h2_redundant_t2_t3_over_q() {
    let vars = VarOrder::new(vec!["t".into()]).unwrap();
    let t = var_q(1, 0);
    let f1 = t.pow(2);
    let f2 = t.pow(3);
    let syz = compute_syzygies_field(
        &[f1.clone(), f2.clone()],
        vars,
        MonomialOrder::Grevlex,
        DEFAULT_MAX_SYZYGY_PAIRS,
    )
    .unwrap();
    assert!(syz.verified);
    assert!(syz.generating_certified);
    assert!(!syz.generators.is_empty());
    // (t, -1) またはその非零定数倍が含まれる（元の syzygy が f1*t - f2 = 0 を生成）
    let eval_at_0: Vec<Vec<Rat>> = syz
        .generators
        .iter()
        .map(|s| {
            s.iter()
                .map(|p| p.eval_at(&[Rat::zero()]).unwrap())
                .collect()
        })
        .collect();
    // t = 0 では s(0) = (0, c) で c != 0 が少なくとも 1 つ存在する
    assert!(eval_at_0.iter().any(|v| v[0].is_zero() && !v[1].is_zero()));
}

#[test]
fn syzygy_h2_z_and_f2_redundant_z2_2z2() {
    // Z 上の (z^2, 2*z^2): 全 syzygy は (-2, 1)（または (2, -1)）
    let vars_z = VarOrder::new(vec!["z".into()]).unwrap();
    let z = Poly::var(1, 0, BigInt::zero());
    let f1 = z.pow(2);
    let f2 = f1.scale(&BigInt::from(2));
    let syz_z = compute_syzygies_z(&[f1, f2], vars_z).unwrap();
    assert!(syz_z.verified);
    assert!(syz_z.generating_certified);
    assert_eq!(syz_z.generators.len(), 1);
    let s0 = syz_z.generators[0][0].constant_value();
    let s1 = syz_z.generators[0][1].constant_value();
    assert_eq!(s0.clone() + s1.clone() * BigInt::from(2), BigInt::zero());
    assert_eq!(s1.abs(), BigInt::from(1));

    // F_2 上の (z^2, 2*z^2) = (z^2, 0): syzygy は (0, 1)
    let p2 = BigUint::from(2u32);
    let zero_fp = FpElem::zero(p2.clone()).unwrap();
    let vars_fp = VarOrder::new(vec!["z".into()]).unwrap();
    let z_fp = Poly::var(1, 0, zero_fp.clone());
    let g1 = z_fp.pow(2);
    let g2 = Poly::zero(1, zero_fp);
    let syz_fp = compute_syzygies_field(
        &[g1, g2],
        vars_fp,
        MonomialOrder::Grevlex,
        DEFAULT_MAX_SYZYGY_PAIRS,
    )
    .unwrap();
    assert!(syz_fp.verified);
    assert!(
        syz_fp
            .generators
            .iter()
            .any(|s| s[0].is_zero() && s[1].constant_value().is_one())
    );
}

#[test]
fn syzygy_h3_dependent_vs_regular_sequence() {
    // H3 (1): f1 = x1 - x0, f2 = x2 - x1, f3 = x0 - x2 => syzygy (1, 1, 1)
    let vars = VarOrder::new(vec!["t".into(), "x0".into(), "x1".into(), "x2".into()]).unwrap();
    let t = var_q(4, 0);
    let x0 = var_q(4, 1);
    let x1 = var_q(4, 2);
    let x2 = var_q(4, 3);
    let f1 = x1.sub(&x0);
    let f2 = x2.sub(&x1);
    let f3 = x0.sub(&x2);
    let syz_dep = compute_syzygies_field(
        &[f1.clone(), f2.clone(), f3],
        vars.clone(),
        MonomialOrder::Grevlex,
        DEFAULT_MAX_SYZYGY_PAIRS,
    )
    .unwrap();
    assert!(syz_dep.verified);
    let origin = vec![Rat::zero(); 4];
    // 原点評価で (1, 1, 1) の非零倍が現れる
    assert!(syz_dep.generators.iter().any(|s| {
        let v: Vec<Rat> = s.iter().map(|p| p.eval_at(&origin).unwrap()).collect();
        !v[0].is_zero() && v[0] == v[1] && v[1] == v[2]
    }));

    // H3 (2): f'3 = x0 - x2 - t => 正則列 (x1-x0, x2-x1, t) と同値、全 syzygy が原点で 0
    let f3_def = x0.sub(&x2).sub(&t);
    let syz_reg = compute_syzygies_field(
        &[f1, f2, f3_def],
        vars,
        MonomialOrder::Grevlex,
        DEFAULT_MAX_SYZYGY_PAIRS,
    )
    .unwrap();
    assert!(syz_reg.verified);
    assert!(!syz_reg.generators.is_empty());
    for s in &syz_reg.generators {
        for p in s {
            assert!(p.eval_at(&origin).unwrap().is_zero());
        }
    }
}

#[test]
fn syzygy_z_rejects_uncertified_nonlinear_family() {
    let vars = VarOrder::new(vec!["x".into(), "y".into()]).unwrap();
    let x = Poly::var(2, 0, BigInt::zero());
    let y = Poly::var(2, 1, BigInt::zero());
    let f1 = x.pow(2).add(&y);
    let f2 = y.pow(2).add(&x);
    let err = compute_syzygies_z(&[f1, f2], vars).unwrap_err();
    assert!(matches!(err, AlgebraError::OutOfScope { .. }));
}

#[test]
fn partial_derivative_and_jacobian_respect_characteristic() {
    let p2 = BigUint::from(2u32);
    let zero_fp = FpElem::zero(p2).unwrap();
    let z = Poly::var(1, 0, zero_fp);
    // d/dz(z^2) = 2z = 0 in F_2, d/dz(z^3) = 3z^2 = z^2 in F_2
    let jac = jacobian_polys(&[z.pow(2), z.pow(3)], 1).unwrap();
    assert!(jac[0][0].is_zero());
    assert_eq!(jac[1][0], z.pow(2));
}

#[test]
fn square_zero_extension_verifies_and_rejects_non_square_zero() {
    // 正常: Q[ε]/(ε^3) ->> Q[ε]/(ε^2) は M = (ε^2), M^2 = 0
    let ok = SquareZeroExtension::truncated_step_field("eps", 1, Rat::zero()).unwrap();
    assert!(ok.square_zero_verified);
    assert_eq!(ok.kernel_dim(), 1);
    let eps2 = vec![Rat::zero(), Rat::zero(), Rat::one()];
    assert_eq!(
        ok.extract_kernel_coords_field(&eps2).unwrap(),
        vec![Rat::one()]
    );

    // 失敗: Q[ε]/(ε^3) ->> Q では M = (ε, ε^2), ε * ε = ε^2 != 0
    let rp = FiniteAlgebra::truncated_univariate("eps", 2, Rat::zero());
    let rb = FiniteAlgebra::base_ring(Rat::zero());
    let proj = vec![vec![Rat::one(), Rat::zero(), Rat::zero()]];
    let err = SquareZeroExtension::new_field(rp, rb, proj).unwrap_err();
    assert!(matches!(err, AlgebraError::OutOfScope { .. }));
}

#[test]
fn local_artin_quotient_handles_free_and_constrained_charts() {
    // H5 比較: 既存関係 Y - T^3 = 0 付き観測環上で J = (Y) の初回失敗次数は ν = 3
    let vars = VarOrder::new(vec!["t".into(), "y".into()]).unwrap();
    let t = var_q(2, 0);
    let y = var_q(2, 1);
    let rel = y.sub(&t.pow(3));
    let origin = vec![Rat::zero(), Rat::zero()];

    let q2 = LocalArtinQuotient::build(
        vars.clone(),
        std::slice::from_ref(&rel),
        &origin,
        2,
        Rat::zero(),
        DEFAULT_MAX_ARTIN_DIM,
    )
    .unwrap();
    // mod m^3 では y = t^3 = 0
    let proj_y_2 = q2.project_poly(&y).unwrap();
    assert!(q2.algebra.is_zero_elem(&proj_y_2));

    let q3 = LocalArtinQuotient::build(
        vars,
        &[rel],
        &origin,
        3,
        Rat::zero(),
        DEFAULT_MAX_ARTIN_DIM,
    )
    .unwrap();
    // mod m^4 では y = t^3 != 0
    let proj_y_3 = q3.project_poly(&y).unwrap();
    assert!(!q3.algebra.is_zero_elem(&proj_y_3));
}

#[test]
fn cochain_complex_z_torsion_and_field_induced_map() {
    // W1: K = [Z --2--> Z] => H^0 = 0, H^1 = Z/2, cocycle [1] は Z で非零・Q で零・位数 2
    let k_z = CochainComplex::new(
        1,
        1,
        0,
        vec![vec![BigInt::from(2)]],
        vec![],
        BigInt::zero(),
    )
    .unwrap();
    let coh_z = k_z.cohomology_z().unwrap();
    assert_eq!(coh_z.h0.free_rank, 0);
    assert_eq!(coh_z.h1.free_rank, 0);
    assert_eq!(coh_z.h1.torsion_invariants, vec![BigInt::from(2)]);
    assert_eq!(coh_z.h1.display("Z"), "Z/2");

    let chk = k_z.check_h1_cocycle_z(&[BigInt::from(1)]).unwrap();
    assert!(chk.is_cocycle);
    assert!(!chk.is_zero_in_z);
    assert!(chk.is_zero_in_q);
    assert_eq!(chk.torsion_order, Some(BigInt::from(2)));

    // F_2 への tensor: d^0 = 0 => H^0 = F_2, H^1 = F_2
    let p2 = BigUint::from(2u32);
    let z2 = FpElem::zero(p2).unwrap();
    let k_f2 = CochainComplex::new(1, 1, 0, vec![vec![z2.clone()]], vec![], z2).unwrap();
    let coh_f2 = k_f2.cohomology_field().unwrap();
    assert_eq!(coh_f2.h0_dim, 1);
    assert_eq!(coh_f2.h1_dim, 1);

    // d^1 * d^0 != 0 は拒否される
    let bad = CochainComplex::new(
        1,
        1,
        1,
        vec![vec![Rat::one()]],
        vec![vec![Rat::one()]],
        Rat::zero(),
    );
    assert!(bad.is_err());

    // 3 辺 cycle と full triangle の包含 cochain 射: H^1(full -> cycle) = 0 -> Q, coker = 1
    let d0_tri = vec![
        vec![-Rat::one(), Rat::one(), Rat::zero()],
        vec![-Rat::one(), Rat::zero(), Rat::one()],
        vec![Rat::zero(), -Rat::one(), Rat::one()],
    ];
    let d1_full = vec![vec![Rat::one(), -Rat::one(), Rat::one()]];
    let c_full = CochainComplex::new(3, 3, 1, d0_tri.clone(), d1_full, Rat::zero()).unwrap();
    let c_cyc = CochainComplex::new(3, 3, 0, d0_tri, vec![], Rat::zero()).unwrap();
    let id3 = vec![
        vec![Rat::one(), Rat::zero(), Rat::zero()],
        vec![Rat::zero(), Rat::one(), Rat::zero()],
        vec![Rat::zero(), Rat::zero(), Rat::one()],
    ];
    let map = CochainMap::new(&c_full, &c_cyc, id3.clone(), id3, vec![]).unwrap();
    let ind = map.induced_field(&c_full, &c_cyc).unwrap();
    assert_eq!(ind.h1.src_dim, 0);
    assert_eq!(ind.h1.dst_dim, 1);
    assert_eq!(ind.h1.coker_dim, 1);
    assert!(!ind.h1.isomorphism);
}

#[test]
fn poly_substitute_and_truncate() {
    let x = var_q(2, 0);
    let y = var_q(2, 1);
    let expr = y.pow(2).add(&const_q(2, 1));
    let sub = expr.substitute(&[x.clone(), x.pow(2)]).unwrap();
    assert_eq!(sub, x.pow(4).add(&const_q(2, 1)));
    assert_eq!(sub.truncate_degree(3), const_q(2, 1));
    let _ = Monomial::one(2);
}
