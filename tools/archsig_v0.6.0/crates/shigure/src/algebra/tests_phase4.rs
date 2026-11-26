//! Phase 4 代数核（`syzygy`・`artin`・`cochain`・`poly` 偏微分/代入）の単体テスト（AC1）。

use crate::algebra::MonomialOrder;
use crate::algebra::artin::{
    DEFAULT_MAX_ARTIN_DIM, FiniteAlgebra, LocalArtinQuotient, SquareZeroExtension,
    enumerate_monomials_up_to,
};
use crate::algebra::cochain::{CochainComplex, CochainMap};
use crate::algebra::poly::{AlgebraError, Monomial, Poly, VarOrder};
use crate::algebra::scalar::{FpElem, Rat, RingCoeff};
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
        &[f1, f2],
        vars,
        MonomialOrder::Grevlex,
        DEFAULT_MAX_SYZYGY_PAIRS,
    )
    .unwrap();
    assert!(syz.verified);
    assert!(syz.generating_certified);
    assert!(!syz.generators.is_empty());
    let eval_at_0: Vec<Vec<Rat>> = syz
        .generators
        .iter()
        .map(|s| {
            s.iter()
                .map(|p| p.eval_at(&[Rat::zero()]).unwrap())
                .collect()
        })
        .collect();
    assert!(eval_at_0.iter().any(|v| v[0].is_zero() && !v[1].is_zero()));
}

#[test]
fn syzygy_nonlinear_twisted_cubic_unit_ideal_and_limit() {
    // 非線形 3 変数 twisted cubic: f1 = x^2 - y, f2 = x*y - z, f3 = y^2 - x*z
    // Hilbert-Burch 関係: (-y, x, -1) と (-z, y, -x)（あるいは線形結合）が全 syzygy を生成
    let vars = VarOrder::new(vec!["x".into(), "y".into(), "z".into()]).unwrap();
    let x = var_q(3, 0);
    let y = var_q(3, 1);
    let z = var_q(3, 2);
    let f1 = x.pow(2).sub(&y);
    let f2 = x.mul(&y).sub(&z);
    let f3 = y.pow(2).sub(&x.mul(&z));
    let syz = compute_syzygies_field(
        &[f1.clone(), f2.clone(), f3.clone()],
        vars.clone(),
        MonomialOrder::Grevlex,
        DEFAULT_MAX_SYZYGY_PAIRS,
    )
    .unwrap();
    assert!(syz.verified);
    assert!(syz.generating_certified);
    // 曲線外の点 (2, 1, 0) では (-y, x, -1) = (-1, 2, -1) と (-z, y, -x) = (0, 1, -2) が独立で階数 2
    let pt_off = vec![Rat::from_int(2), Rat::from_int(1), Rat::zero()];
    let rows_off: Vec<Vec<Rat>> = syz
        .generators
        .iter()
        .map(|s| s.iter().map(|p| p.eval_at(&pt_off).unwrap()).collect())
        .collect();
    let rref_off = crate::algebra::artin::rref_field(&rows_off, 3, &Rat::zero()).unwrap();
    assert_eq!(rref_off.rank, 2);
    // 曲線上の滑らかな点 (1, 1, 1) では 2 本の Hilbert-Burch syzygy がともに (-1, 1, -1) に一致し階数 1
    let pt_on = vec![Rat::one(), Rat::one(), Rat::one()];
    let rows_on: Vec<Vec<Rat>> = syz
        .generators
        .iter()
        .map(|s| s.iter().map(|p| p.eval_at(&pt_on).unwrap()).collect())
        .collect();
    let rref_on = crate::algebra::artin::rref_field(&rows_on, 3, &Rat::zero()).unwrap();
    assert_eq!(rref_on.rank, 1);

    // 1 ∈ I のケース: (x, 1 - x) => syzygy (1 - x, -x)
    let unit_syz = compute_syzygies_field(
        &[x.clone(), const_q(3, 1).sub(&x)],
        vars.clone(),
        MonomialOrder::Grevlex,
        DEFAULT_MAX_SYZYGY_PAIRS,
    )
    .unwrap();
    assert!(unit_syz.verified);
    assert!(!unit_syz.generators.is_empty());

    // max_pairs = 0 でペア超過エラー
    let err = compute_syzygies_field(&[f1, f2, f3], vars, MonomialOrder::Grevlex, 0).unwrap_err();
    assert!(matches!(err, AlgebraError::OutOfScope { .. }));
}

#[test]
fn syzygy_h2_z_and_f2_and_z_cases_2_3() {
    // Case 1 (Z 単項式): (z^2, 2*z^2) => (-2, 1)
    let vars_z = VarOrder::new(vec!["z".into()]).unwrap();
    let z = Poly::var(1, 0, BigInt::zero());
    let f1 = z.pow(2);
    let f2 = f1.scale(&BigInt::from(2));
    let syz_z = compute_syzygies_z(&[f1, f2], vars_z).unwrap();
    assert!(syz_z.verified);
    assert_eq!(syz_z.generators.len(), 1);
    let s0 = syz_z.generators[0][0].constant_value();
    let s1 = syz_z.generators[0][1].constant_value();
    assert_eq!(s0 + &s1 * BigInt::from(2), BigInt::zero());
    assert_eq!(s1.abs(), BigInt::from(1));

    // Case 2 (Z 共通原始多項式倍): (2*(x+y), 3*(x+y)) => (3, -2)
    let vars_xy = VarOrder::new(vec!["x".into(), "y".into()]).unwrap();
    let x = Poly::var(2, 0, BigInt::zero());
    let y = Poly::var(2, 1, BigInt::zero());
    let h = x.add(&y);
    let syz_c2 = compute_syzygies_z(
        &[h.scale(&BigInt::from(2)), h.scale(&BigInt::from(3))],
        vars_xy.clone(),
    )
    .unwrap();
    assert!(syz_c2.verified);
    assert_eq!(syz_c2.generators.len(), 1);

    // Case 3 (Z unimodular 線形族): (x - y, y - x, x) => 受理され定数 syzygy + Koszul を生成
    let syz_c3 = compute_syzygies_z(&[x.sub(&y), y.sub(&x), x.clone()], vars_xy.clone()).unwrap();
    assert!(syz_c3.verified);
    assert!(syz_c3.generators.len() >= 2);

    // Case 3 負例 (非 unimodular 線形族: Smith 対角 2): (2*x + 2*y, 2*x - 2*y) => 拒否
    let err_non_uni = compute_syzygies_z(
        &[
            x.scale(&BigInt::from(2)).add(&y.scale(&BigInt::from(2))),
            x.scale(&BigInt::from(2)).sub(&y.scale(&BigInt::from(2))),
        ],
        vars_xy,
    )
    .unwrap_err();
    assert!(matches!(err_non_uni, AlgebraError::OutOfScope { .. }));

    // F_2 上の (z^2, 0) => (0, 1)
    let p2 = BigUint::from(2u32);
    let zero_fp = FpElem::zero(p2).unwrap();
    let vars_fp = VarOrder::new(vec!["z".into()]).unwrap();
    let z_fp = Poly::var(1, 0, zero_fp.clone());
    let syz_fp = compute_syzygies_field(
        &[z_fp.pow(2), Poly::zero(1, zero_fp)],
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
    assert!(syz_dep.generators.iter().any(|s| {
        let v: Vec<Rat> = s.iter().map(|p| p.eval_at(&origin).unwrap()).collect();
        !v[0].is_zero() && v[0] == v[1] && v[1] == v[2]
    }));

    let f3_def = x0.sub(&x2).sub(&t);
    let syz_reg = compute_syzygies_field(
        &[f1, f2, f3_def],
        vars,
        MonomialOrder::Grevlex,
        DEFAULT_MAX_SYZYGY_PAIRS,
    )
    .unwrap();
    assert!(syz_reg.verified);
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
    let err = compute_syzygies_z(&[x.pow(2).add(&y), y.pow(2).add(&x)], vars).unwrap_err();
    assert!(matches!(err, AlgebraError::OutOfScope { .. }));
}

#[test]
fn partial_derivative_and_jacobian_respect_characteristic() {
    let p2 = BigUint::from(2u32);
    let zero_fp = FpElem::zero(p2).unwrap();
    let z = Poly::var(1, 0, zero_fp);
    let jac = jacobian_polys(&[z.pow(2), z.pow(3)], 1).unwrap();
    assert!(jac[0][0].is_zero());
    assert_eq!(jac[1][0], z.pow(2));
}

#[test]
fn square_zero_extension_field_z_and_rejections() {
    // Field 正常: Q[ε]/(ε^3) ->> Q[ε]/(ε^2)
    let ok = SquareZeroExtension::truncated_step_field("eps", 1, Rat::zero()).unwrap();
    assert!(ok.square_zero_verified());
    assert_eq!(ok.kernel_dim(), 1);
    let eps2 = vec![Rat::zero(), Rat::zero(), Rat::one()];
    assert_eq!(
        ok.extract_kernel_coords_field(&eps2).unwrap(),
        vec![Rat::one()]
    );

    // Z 正常: Z[ε]/(ε^3) ->> Z[ε]/(ε^2)
    let ok_z = SquareZeroExtension::truncated_step_z("eps", 1).unwrap();
    assert!(ok_z.square_zero_verified());
    assert_eq!(ok_z.kernel_dim(), 1);
    let eps2_z = vec![BigInt::zero(), BigInt::zero(), BigInt::from(5)];
    assert_eq!(
        ok_z.extract_kernel_coords_z(&eps2_z).unwrap(),
        vec![BigInt::from(5)]
    );

    // 失敗 1: M^2 != 0 (Q[ε]/(ε^3) ->> Q)
    let rp = FiniteAlgebra::truncated_univariate("eps", 2, Rat::zero()).unwrap();
    let rb = FiniteAlgebra::base_ring(Rat::zero());
    let proj = vec![vec![Rat::one(), Rat::zero(), Rat::zero()]];
    assert!(matches!(
        SquareZeroExtension::new_field(rp, rb.clone(), proj),
        Err(AlgebraError::OutOfScope { .. })
    ));

    // 失敗 2: 非全射射影 (Z[ε]/(ε^2) -> Z で 1 -> 2)
    let rp_z = FiniteAlgebra::truncated_univariate("eps", 1, BigInt::zero()).unwrap();
    let rb_z = FiniteAlgebra::base_ring(BigInt::zero());
    assert!(matches!(
        SquareZeroExtension::new_z(rp_z, rb_z, vec![vec![BigInt::from(2), BigInt::zero()]]),
        Err(AlgebraError::OutOfScope { .. })
    ));

    // 失敗 3: 異なる F_p 法の混在は panic せず DomainMismatch
    let z2 = FpElem::zero(BigUint::from(2u32)).unwrap();
    let z3 = FpElem::zero(BigUint::from(3u32)).unwrap();
    let rp_2 = FiniteAlgebra::truncated_univariate("e", 1, z2.clone()).unwrap();
    let rb_3 = FiniteAlgebra::base_ring(z3);
    let err =
        SquareZeroExtension::new_field(rp_2, rb_3, vec![vec![z2.one_like(), z2]]).unwrap_err();
    assert!(matches!(err, AlgebraError::DomainMismatch { .. }));

    // 失敗 4: 次元上限超過・オーバーフローは fail-closed に OutOfScope
    assert!(matches!(
        FiniteAlgebra::truncated_univariate("e", DEFAULT_MAX_ARTIN_DIM, Rat::zero()),
        Err(AlgebraError::OutOfScope { .. })
    ));
    assert!(matches!(
        SquareZeroExtension::truncated_step_field("e", usize::MAX, Rat::zero()),
        Err(AlgebraError::OutOfScope { .. })
    ));
    assert!(matches!(
        SquareZeroExtension::truncated_step_z("e", DEFAULT_MAX_ARTIN_DIM),
        Err(AlgebraError::OutOfScope { .. })
    ));
}

#[test]
fn local_artin_quotient_nonzero_base_violations_and_bounds() {
    // 非零基点 a = (1, 1) で I_O = (y - t^2) 上の J = (y - 1):
    // t = 1 + w_t, y = 1 + w_y => w_y = 2 w_t + w_t^2 なので mod m^2 で y - 1 = 2 w_t != 0 (ν = 1)
    let vars = VarOrder::new(vec!["t".into(), "y".into()]).unwrap();
    let t = var_q(2, 0);
    let y = var_q(2, 1);
    let rel = y.sub(&t.pow(2));
    let pt = vec![Rat::one(), Rat::one()];
    let q1 = LocalArtinQuotient::build(
        vars.clone(),
        std::slice::from_ref(&rel),
        &pt,
        1,
        Rat::zero(),
        DEFAULT_MAX_ARTIN_DIM,
    )
    .unwrap();
    let proj = q1.project_poly(&y.sub(&const_q(2, 1))).unwrap();
    assert!(!q1.algebra.is_zero_elem(&proj));

    // I_O を満たさない基点 (1, 0) は拒否
    assert!(matches!(
        LocalArtinQuotient::build(
            vars.clone(),
            std::slice::from_ref(&rel),
            &[Rat::one(), Rat::zero()],
            1,
            Rat::zero(),
            DEFAULT_MAX_ARTIN_DIM,
        ),
        Err(AlgebraError::OutOfScope { .. })
    ));

    // max_dim 上限超過は OutOfScope
    assert!(matches!(
        LocalArtinQuotient::build(vars, &[rel], &pt, 3, Rat::zero(), 2),
        Err(AlgebraError::OutOfScope { .. })
    ));

    // num_vars == 0 でも停止し max_dim = 0 のみ OutOfScope
    assert_eq!(enumerate_monomials_up_to(0, 100, 1).unwrap().len(), 1);
    assert!(matches!(
        enumerate_monomials_up_to(0, 1, 0),
        Err(AlgebraError::OutOfScope { .. })
    ));
}

#[test]
fn cochain_complex_z_torsion_nonzero_d1_and_nontrivial_induced_maps() {
    // 1. Z 複体で d^0 = [0], d^1 = [2] => H^0 = Z, H^1 = 0, H^2 = Z/2
    let c_h2_tor = CochainComplex::new(
        1,
        1,
        1,
        vec![vec![BigInt::zero()]],
        vec![vec![BigInt::from(2)]],
        BigInt::zero(),
    )
    .unwrap();
    let coh_h2 = c_h2_tor.cohomology_z().unwrap();
    assert_eq!(coh_h2.h0.free_rank, 1);
    assert_eq!(coh_h2.h1.free_rank, 0);
    assert_eq!(coh_h2.h2.torsion_invariants, vec![BigInt::from(2)]);
    assert_eq!(coh_h2.h2.display("Z"), "Z/2");

    // 2. W1: K = [Z --2--> Z] => H^1 = Z/2, cocycle [1] は Z で非零・Q で零・位数 2
    let k_z =
        CochainComplex::new(1, 1, 0, vec![vec![BigInt::from(2)]], vec![], BigInt::zero()).unwrap();
    let chk = k_z.check_h1_cocycle_z(&[BigInt::from(1)]).unwrap();
    assert!(chk.is_cocycle && !chk.is_zero_in_z && chk.is_zero_in_q);
    assert_eq!(chk.torsion_order, Some(BigInt::from(2)));

    // 3. 非自明な src_dim > 0 かつ dst_dim > 0 の CochainMap::induced_field（H^0, H^1, H^2 すべて検証）
    // 3 辺 cycle への恒等射 + 非零 2-cochain 付き（dim2 = 1, d1 = 0 => H^0 = Q, H^1 = Q, H^2 = Q）
    let d0_tri = vec![
        vec![-Rat::one(), Rat::one(), Rat::zero()],
        vec![-Rat::one(), Rat::zero(), Rat::one()],
        vec![Rat::zero(), -Rat::one(), Rat::one()],
    ];
    let d1_zero = vec![vec![Rat::zero(), Rat::zero(), Rat::zero()]];
    let c_cyc = CochainComplex::new(3, 3, 1, d0_tri, d1_zero, Rat::zero()).unwrap();
    let coh_cyc = c_cyc.cohomology_field().unwrap();
    assert_eq!((coh_cyc.h0_dim, coh_cyc.h1_dim, coh_cyc.h2_dim), (1, 1, 1));

    // check_h1_cocycle_field: 周期和 != 0 なら非零類、(1, 1, 0) = d^0(0, 1, 1) は零類
    let nz = c_cyc
        .check_h1_cocycle_field(&coh_cyc, &[Rat::one(), Rat::zero(), Rat::zero()])
        .unwrap();
    assert!(nz.is_cocycle && !nz.is_zero_class && !nz.class_coords[0].is_zero());
    let zr = c_cyc
        .check_h1_cocycle_field(&coh_cyc, &[Rat::one(), Rat::one(), Rat::zero()])
        .unwrap();
    assert!(zr.is_cocycle && zr.is_zero_class && zr.coboundary_witness.is_some());

    // 恒等射は H^0, H^1, H^2 すべて同型
    let id3 = vec![
        vec![Rat::one(), Rat::zero(), Rat::zero()],
        vec![Rat::zero(), Rat::one(), Rat::zero()],
        vec![Rat::zero(), Rat::zero(), Rat::one()],
    ];
    let id1 = vec![vec![Rat::one()]];
    let map_id = CochainMap::new(&c_cyc, &c_cyc, id3.clone(), id3, id1).unwrap();
    let ind = map_id.induced_field(&c_cyc, &c_cyc).unwrap();
    assert!(ind.h0.isomorphism && ind.h1.isomorphism && ind.h2.isomorphism);
    assert_eq!((ind.h0.im_dim, ind.h1.im_dim, ind.h2.im_dim), (1, 1, 1));

    // 列数不一致は正しい expected/actual の ArityMismatch
    let bad_col = CochainComplex::new(2, 1, 0, vec![vec![Rat::one()]], vec![], Rat::zero());
    assert_eq!(
        bad_col,
        Err(AlgebraError::ArityMismatch {
            expected: 2,
            actual: 1
        })
    );

    // d^1 * d^0 != 0 は拒否
    assert!(
        CochainComplex::new(
            1,
            1,
            1,
            vec![vec![Rat::one()]],
            vec![vec![Rat::one()]],
            Rat::zero(),
        )
        .is_err()
    );
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

#[test]
fn boundary_checks_z_kernel_arity_and_cochain_map_ring_mismatch() {
    // extract_kernel_coords_z は次元不一致を ArityMismatch として返す
    let ext_z = SquareZeroExtension::truncated_step_z("eps", 0).unwrap();
    assert_eq!(
        ext_z.extract_kernel_coords_z(&[BigInt::from(1)]),
        Err(AlgebraError::ArityMismatch {
            expected: 2,
            actual: 1
        })
    );
    assert_eq!(
        ext_z.extract_kernel_coords_z(&[BigInt::from(1), BigInt::from(0), BigInt::from(9)]),
        Err(AlgebraError::ArityMismatch {
            expected: 2,
            actual: 3
        })
    );

    // CochainMap::new は異なる法 Fp の成分混入を panic せず DomainMismatch にする
    let z2 = FpElem::zero(BigUint::from(2u32)).unwrap();
    let one3 = FpElem::one(BigUint::from(3u32)).unwrap();
    let c2 = CochainComplex::new(1, 0, 0, vec![], vec![], z2.clone()).unwrap();
    assert!(matches!(
        CochainMap::new(&c2, &c2, vec![vec![one3]], vec![], vec![]),
        Err(AlgebraError::DomainMismatch { .. })
    ));

    // CochainMap::induced_field は別複体対で可換性が破れる場合に fail-closed に OutOfScope を返す
    let c_zero = CochainComplex::new(
        1,
        2,
        0,
        vec![vec![Rat::zero()], vec![Rat::zero()]],
        vec![],
        Rat::zero(),
    )
    .unwrap();
    let c_nonzero = CochainComplex::new(
        1,
        2,
        0,
        vec![vec![Rat::one()], vec![Rat::zero()]],
        vec![],
        Rat::zero(),
    )
    .unwrap();
    let f_for_zero = CochainMap::new(
        &c_zero,
        &c_zero,
        vec![vec![Rat::zero()]],
        vec![
            vec![Rat::zero(), Rat::zero()],
            vec![Rat::one(), Rat::zero()],
        ],
        vec![],
    )
    .unwrap();
    assert!(matches!(
        f_for_zero.induced_field(&c_nonzero, &c_nonzero),
        Err(AlgebraError::OutOfScope { .. })
    ));

    // embed_kernel は異法 FpElem（非零・零の双方）を panic/黙過せず DomainMismatch にする
    let ext_f2 = SquareZeroExtension::truncated_step_field("eps", 0, z2).unwrap();
    let one3_b = FpElem::one(BigUint::from(3u32)).unwrap();
    let zero3_b = FpElem::zero(BigUint::from(3u32)).unwrap();
    assert!(matches!(
        ext_f2.embed_kernel(&[one3_b]),
        Err(AlgebraError::DomainMismatch { .. })
    ));
    assert!(matches!(
        ext_f2.embed_kernel(&[zero3_b]),
        Err(AlgebraError::DomainMismatch { .. })
    ));

    // check_h1_cocycle_field は別次元複体の FieldCohomology を panic せず ArityMismatch にする
    let c_dim1 = CochainComplex::new(0, 1, 0, vec![vec![]], vec![], Rat::zero()).unwrap();
    let coh_dim2 = c_zero.cohomology_field().unwrap();
    assert_eq!(
        c_dim1.check_h1_cocycle_field(&coh_dim2, &[Rat::one()]),
        Err(AlgebraError::ArityMismatch {
            expected: 1,
            actual: 2
        })
    );
}
