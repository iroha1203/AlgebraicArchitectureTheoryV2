//! 値合流 Mayer–Vietoris 長完全列・多段合流順序独立性（G-142 C2–C4・W2）
//! および診断次元実現 $V(g_1, \dots, g_r) \cap D(h)$（G-142 D1–D2）。

use crate::algebra::cochain::{CochainComplex, CochainMap, mat_mul};
use crate::algebra::linear::smith_normal_form_z;
use crate::algebra::poly::{AlgebraError, Poly};
use crate::algebra::poly_expr::ExprBindings;
use crate::algebra::scalar::{FpElem, Rat, RingCoeff};
use crate::algebra::syzygy::FieldCoeff;
use crate::ir::diagnostics::{
    ChartSupportSpec, CollisionComparisonSpec, DimensionRealizationSpec, NerveEdgeSpec,
    NerveFaceSpec, SupportedNerveSpec,
};
use crate::ir::result::SilenceReason;
use crate::ir::result_phase4::{
    CollisionMayerVietorisResult, DimensionProbePointResult, DimensionRealizationResult,
};
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::solver::diagnostics::{
    ComputedNerve, DiagnosticComplexData, build_diagnostic_complex, compute_nerve,
    evaluate_complex_over_domain, lift_mat_z_to_fp, lift_mat_z_to_q, map_diag_alg_err,
};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::collections::{BTreeMap, BTreeSet};

/// 粗化 partition `π -> π'` の単射合流射 `r` と余核複体 `Q` の長完全列を計算する（C2–C4）。
pub(crate) fn compute_collision_mv(
    col: &CollisionComparisonSpec,
    nerve: &ComputedNerve,
    reading_map: Option<&BTreeMap<&str, &str>>,
    diag_coeff: &CoeffDomain,
) -> Result<CollisionMayerVietorisResult, SilenceReason> {
    let fine_cpx = build_partition_complex(nerve, &col.fine_partition, reading_map)?;
    let coarse_cpx = build_partition_complex(nerve, &col.coarse_partition, reading_map)?;

    let (r0, r1, r2) = build_coarsening_map_matrices(
        &col.coarse_partition,
        &col.fine_partition,
        &coarse_cpx,
        &fine_cpx,
    )?;

    // 余核複体 Q = coker(r) を構成（二値合流では C^\bullet(K_a ∩ K_b) と完全一致、一般合流では C4 の完全列を与える）。
    let (q_cpx, rho0, rho1, rho2) = build_cokernel_complex_and_rho(
        nerve,
        &col.coarse_partition,
        &col.fine_partition,
        &fine_cpx,
    )?;

    // r ∘ rho == 0 の確認（短完全列 0 -> C(coarse) --r--> C(fine) --rho--> Q -> 0）。
    for (rho, r, cols) in [
        (&rho0, &r0, coarse_cpx.coords0.len()),
        (&rho1, &r1, coarse_cpx.coords1.len()),
        (&rho2, &r2, coarse_cpx.coords2.len()),
    ] {
        let comp = mat_mul(rho, r, cols, &BigInt::zero());
        if comp.iter().any(|row| row.iter().any(|v| !v.is_zero())) {
            return Err(SilenceReason::DiagnosticsStratificationOutOfScope {
                detail: format!("exact sequence condition rho * r == 0 violated in `{}`", col.label),
            });
        }
    }

    let (ker_h1_r, coker_h1_r, coker_h0_rho, im_h1_rho, h1_r_iso, mv_ok) = match diag_coeff {
        CoeffDomain::Q => {
            eval_mv_field(
                &coarse_cpx,
                &fine_cpx,
                &q_cpx,
                (&lift_mat_z_to_q(&r0), &lift_mat_z_to_q(&r1), &lift_mat_z_to_q(&r2)),
                (&lift_mat_z_to_q(&rho0), &lift_mat_z_to_q(&rho1), &lift_mat_z_to_q(&rho2)),
                Rat::zero(),
            )?
        }
        CoeffDomain::Fp(p) => {
            let Some(zero_fp) = FpElem::zero(p.clone()) else {
                return Err(SilenceReason::UnsupportedCoeffRing {
                    domain: diag_coeff.clone(),
                    detail: format!("modulus {p} is not prime"),
                });
            };
            eval_mv_field(
                &coarse_cpx,
                &fine_cpx,
                &q_cpx,
                (
                    &lift_mat_z_to_fp(&r0, p),
                    &lift_mat_z_to_fp(&r1, p),
                    &lift_mat_z_to_fp(&r2, p),
                ),
                (
                    &lift_mat_z_to_fp(&rho0, p),
                    &lift_mat_z_to_fp(&rho1, p),
                    &lift_mat_z_to_fp(&rho2, p),
                ),
                zero_fp,
            )?
        }
        CoeffDomain::Z => eval_mv_z(
            &coarse_cpx,
            &fine_cpx,
            &q_cpx,
            (&r0, &r1, &r2),
            (&rho0, &rho1, &rho2),
        )?,
    };

    // C2: 多段合流経路の合成一致検査。
    let multi_stage_order_independent = if col.alternative_merge_paths.is_empty() {
        None
    } else {
        let mut all_match = true;
        for path in &col.alternative_merge_paths {
            let mut cur_part: &[Vec<String>] = &col.fine_partition;
            let mut cur_cpx = fine_cpx.clone();
            // 合成方向: fine <- step_0 <- ... <- coarse (r は coarse -> fine)
            let mut steps: Vec<&[Vec<String>]> = Vec::with_capacity(path.len() + 2);
            steps.push(&col.fine_partition);
            for s in path {
                steps.push(s.as_slice());
            }
            steps.push(&col.coarse_partition);

            // 右（coarse）から左（fine）へ合成: r_{coarse -> fine} = r_{s1 -> fine} * ... * r_{coarse -> sk}
            let mut acc0: Option<Vec<Vec<BigInt>>> = None;
            let mut acc1: Option<Vec<Vec<BigInt>>> = None;
            let mut acc2: Option<Vec<Vec<BigInt>>> = None;
            let mut cpx_list = Vec::with_capacity(steps.len());
            for st in &steps {
                cpx_list.push(build_partition_complex(nerve, st, reading_map)?);
            }
            for idx in 0..(steps.len() - 1) {
                let (m0, m1, m2) = build_coarsening_map_matrices(
                    steps[idx + 1],
                    steps[idx],
                    &cpx_list[idx + 1],
                    &cpx_list[idx],
                )?;
                let c0_cols = cpx_list[idx + 1].coords0.len();
                let c1_cols = cpx_list[idx + 1].coords1.len();
                let c2_cols = cpx_list[idx + 1].coords2.len();
                acc0 = Some(match acc0 {
                    None => m0,
                    Some(prev) => mat_mul(&prev, &m0, c0_cols, &BigInt::zero()),
                });
                acc1 = Some(match acc1 {
                    None => m1,
                    Some(prev) => mat_mul(&prev, &m1, c1_cols, &BigInt::zero()),
                });
                acc2 = Some(match acc2 {
                    None => m2,
                    Some(prev) => mat_mul(&prev, &m2, c2_cols, &BigInt::zero()),
                });
                let _ = (cur_part, &cur_cpx);
                cur_part = steps[idx + 1];
                cur_cpx = cpx_list[idx + 1].clone();
            }
            if acc0.as_ref() != Some(&r0)
                || acc1.as_ref() != Some(&r1)
                || acc2.as_ref() != Some(&r2)
            {
                all_match = false;
                break;
            }
        }
        Some(all_match)
    };

    Ok(CollisionMayerVietorisResult {
        label: col.label.clone(),
        ker_h1_r_dim: ker_h1_r,
        coker_h1_r_dim: coker_h1_r,
        coker_h0_rho_dim: coker_h0_rho,
        im_h1_rho_dim: im_h1_rho,
        mayer_vietoris_identity_verified: mv_ok,
        h1_r_is_isomorphism: h1_r_iso,
        multi_stage_order_independent,
    })
}

type MatTripleRef<'a, C> = (&'a [Vec<C>], &'a [Vec<C>], &'a [Vec<C>]);
type IntMatTriple = (Vec<Vec<BigInt>>, Vec<Vec<BigInt>>, Vec<Vec<BigInt>>);
type CokernelBundle = (
    DiagnosticComplexData,
    Vec<Vec<BigInt>>,
    Vec<Vec<BigInt>>,
    Vec<Vec<BigInt>>,
);

fn eval_mv_field<C: FieldCoeff>(
    coarse_data: &DiagnosticComplexData,
    fine_data: &DiagnosticComplexData,
    q_data: &DiagnosticComplexData,
    r_mats: MatTripleRef<'_, C>,
    rho_mats: MatTripleRef<'_, C>,
    zero: C,
) -> Result<(usize, usize, usize, usize, bool, bool), SilenceReason> {
    let c_cpx = CochainComplex::new(
        coarse_data.coords0.len(),
        coarse_data.coords1.len(),
        coarse_data.coords2.len(),
        to_field_mat(&coarse_data.d0_z, &zero),
        to_field_mat(&coarse_data.d1_z, &zero),
        zero.clone(),
    )
    .map_err(map_diag_alg_err)?;
    let f_cpx = CochainComplex::new(
        fine_data.coords0.len(),
        fine_data.coords1.len(),
        fine_data.coords2.len(),
        to_field_mat(&fine_data.d0_z, &zero),
        to_field_mat(&fine_data.d1_z, &zero),
        zero.clone(),
    )
    .map_err(map_diag_alg_err)?;
    let q_cpx = CochainComplex::new(
        q_data.coords0.len(),
        q_data.coords1.len(),
        q_data.coords2.len(),
        to_field_mat(&q_data.d0_z, &zero),
        to_field_mat(&q_data.d1_z, &zero),
        zero,
    )
    .map_err(map_diag_alg_err)?;

    let r_map = CochainMap::new(
        &c_cpx,
        &f_cpx,
        r_mats.0.to_vec(),
        r_mats.1.to_vec(),
        r_mats.2.to_vec(),
    )
    .map_err(map_diag_alg_err)?;
    let rho_map = CochainMap::new(
        &f_cpx,
        &q_cpx,
        rho_mats.0.to_vec(),
        rho_mats.1.to_vec(),
        rho_mats.2.to_vec(),
    )
    .map_err(map_diag_alg_err)?;

    let ind_r = r_map.induced_field(&c_cpx, &f_cpx).map_err(map_diag_alg_err)?;
    let ind_rho = rho_map.induced_field(&f_cpx, &q_cpx).map_err(map_diag_alg_err)?;

    let ker_h1_r = ind_r.h1.ker_dim;
    let coker_h1_r = ind_r.h1.coker_dim;
    let coker_h0_rho = ind_rho.h0.coker_dim;
    let im_h1_rho = ind_rho.h1.im_dim;
    let h1_r_iso = ind_r.h1.isomorphism;
    let mv_ok = ker_h1_r == coker_h0_rho
        && coker_h1_r == im_h1_rho
        && (h1_r_iso == (coker_h0_rho == 0 && im_h1_rho == 0));
    Ok((ker_h1_r, coker_h1_r, coker_h0_rho, im_h1_rho, h1_r_iso, mv_ok))
}

fn eval_mv_z(
    coarse_data: &DiagnosticComplexData,
    fine_data: &DiagnosticComplexData,
    q_data: &DiagnosticComplexData,
    r_mats: MatTripleRef<'_, BigInt>,
    rho_mats: MatTripleRef<'_, BigInt>,
) -> Result<(usize, usize, usize, usize, bool, bool), SilenceReason> {
    // まず Z 上で cochain 可換性と torsion の有無を厳密検証する。
    let c_z = CochainComplex::new(
        coarse_data.coords0.len(),
        coarse_data.coords1.len(),
        coarse_data.coords2.len(),
        coarse_data.d0_z.clone(),
        coarse_data.d1_z.clone(),
        BigInt::zero(),
    )
    .map_err(map_diag_alg_err)?;
    let f_z = CochainComplex::new(
        fine_data.coords0.len(),
        fine_data.coords1.len(),
        fine_data.coords2.len(),
        fine_data.d0_z.clone(),
        fine_data.d1_z.clone(),
        BigInt::zero(),
    )
    .map_err(map_diag_alg_err)?;
    let q_z = CochainComplex::new(
        q_data.coords0.len(),
        q_data.coords1.len(),
        q_data.coords2.len(),
        q_data.d0_z.clone(),
        q_data.d1_z.clone(),
        BigInt::zero(),
    )
    .map_err(map_diag_alg_err)?;

    let _r_z = CochainMap::new(
        &c_z,
        &f_z,
        r_mats.0.to_vec(),
        r_mats.1.to_vec(),
        r_mats.2.to_vec(),
    )
    .map_err(map_diag_alg_err)?;
    let _rho_z = CochainMap::new(
        &f_z,
        &q_z,
        rho_mats.0.to_vec(),
        rho_mats.1.to_vec(),
        rho_mats.2.to_vec(),
    )
    .map_err(map_diag_alg_err)?;

    let coh_c = c_z.cohomology_z().map_err(map_diag_alg_err)?;
    let coh_f = f_z.cohomology_z().map_err(map_diag_alg_err)?;
    let _coh_q = q_z.cohomology_z().map_err(map_diag_alg_err)?;

    // H^1(coarse) または H^1(fine) に Z-torsion がある場合は torsion-free SNF 判定外として fail-closed 沈黙する。
    // 注意: H^1(Q_Z) の torsion は H^1(r) の同型性を阻害しない（例: RP^2 の 3-cover で H^1(C)=H^1(F)=0, H^1(Q)=Z/2）。
    if !coh_c.h1.torsion_invariants.is_empty() || !coh_f.h1.torsion_invariants.is_empty() {
        return Err(SilenceReason::DiagnosticsStratificationOutOfScope {
            detail: "Z-torsion in H^1 of coarse/fine diagnostic complex is outside torsion-free SNF isomorphism check".to_owned(),
        });
    }

    // 有理階数の計算（Q 上の長完全列）。
    let (ker_q, coker_q, coker_h0_q, im_h1_q, h1_iso_q, mv_q) = eval_mv_field(
        coarse_data,
        fine_data,
        q_data,
        (
            &lift_mat_z_to_q(r_mats.0),
            &lift_mat_z_to_q(r_mats.1),
            &lift_mat_z_to_q(r_mats.2),
        ),
        (
            &lift_mat_z_to_q(rho_mats.0),
            &lift_mat_z_to_q(rho_mats.1),
            &lift_mat_z_to_q(rho_mats.2),
        ),
        Rat::zero(),
    )?;

    // Z 上の H^1 同型（torsion-free 確認済みなので Q 同型かつ SNF 不変因子すべて 1 が必要十分）。
    let z_iso = if !h1_iso_q {
        false
    } else if coh_c.h1.free_rank == 0 {
        true
    } else {
        // Z-自由 H^1(coarse) -> H^1(fine) の商同型を SNF で確認:
        // im(r1(Z^1_c)) + B^1_f == Z^1_f を確認する。
        let z1_f = &coh_f.h1_cycle_basis;
        let z1_c = &coh_c.h1_cycle_basis;
        let mut combined_cols: Vec<Vec<BigInt>> = Vec::new();
        for c in 0..f_z.dim0() {
            combined_cols.push(f_z.d0().iter().map(|row| row[c].clone()).collect());
        }
        for v in z1_c {
            combined_cols.push(crate::algebra::cochain::mat_vec(r_mats.1, v, &BigInt::zero()));
        }
        let f_dim1 = f_z.dim1();
        let mut z1f_mat = vec![vec![BigInt::zero(); z1_f.len()]; f_dim1];
        for (col, v) in z1_f.iter().enumerate() {
            for (row, val) in v.iter().enumerate() {
                z1f_mat[row][col] = val.clone();
            }
        }
        let snf_z1f = smith_normal_form_z(&z1f_mat, z1_f.len()).map_err(map_diag_alg_err)?;
        let mut coords_mat = vec![vec![BigInt::zero(); combined_cols.len()]; z1_f.len()];
        for (col, vec_col) in combined_cols.iter().enumerate() {
            let u_rhs = crate::algebra::cochain::mat_vec(&snf_z1f.u, vec_col, &BigInt::zero());
            let mut y = vec![BigInt::zero(); z1_f.len()];
            for i in 0..snf_z1f.rank {
                y[i] = &u_rhs[i] / &snf_z1f.diagonals[i];
            }
            let coord = crate::algebra::cochain::mat_vec(&snf_z1f.v, &y, &BigInt::zero());
            for row in 0..z1_f.len() {
                coords_mat[row][col] = coord[row].clone();
            }
        }
        let snf_im =
            smith_normal_form_z(&coords_mat, combined_cols.len()).map_err(map_diag_alg_err)?;
        snf_im.rank == z1_f.len() && snf_im.diagonals.iter().all(|d| *d == BigInt::one())
    };

    let mv_ok = mv_q;
    Ok((ker_q, coker_q, coker_h0_q, im_h1_q, z_iso, mv_ok))
}

fn to_field_mat<C: FieldCoeff>(mat: &[Vec<BigInt>], zero: &C) -> Vec<Vec<C>> {
    let one = zero.one_like();
    let neg_one = zero.sub_ref(&one);
    mat.iter()
        .map(|row| {
            row.iter()
                .map(|v| {
                    if v.is_zero() {
                        zero.zero_like()
                    } else if *v == BigInt::one() {
                        one.clone()
                    } else if *v == -BigInt::one() {
                        neg_one.clone()
                    } else {
                        // 一般整数倍（反復加算、ここでは基本 -1,0,1）
                        let neg = v < &BigInt::zero();
                        let abs = if neg { -v } else { v.clone() };
                        let mut acc = zero.zero_like();
                        let mut base = one.clone();
                        let mut n = abs;
                        while !n.is_zero() {
                            if &n % 2 == BigInt::one() {
                                acc = acc.add_ref(&base);
                            }
                            base = base.add_ref(&base);
                            n >>= 1;
                        }
                        if neg { zero.sub_ref(&acc) } else { acc }
                    }
                })
                .collect()
        })
        .collect()
}

fn build_partition_complex(
    nerve: &ComputedNerve,
    partition: &[Vec<String>],
    reading_map: Option<&BTreeMap<&str, &str>>,
) -> Result<DiagnosticComplexData, SilenceReason> {
    let mut vals: BTreeMap<String, String> = BTreeMap::new();
    for (bi, block) in partition.iter().enumerate() {
        let label = format!("b{bi}");
        for s in block {
            let tgt = reading_map
                .and_then(|m| m.get(s.as_str()).copied())
                .unwrap_or(s.as_str());
            if let Some(prev) = vals.get(tgt)
                && prev != &label
            {
                return Err(SilenceReason::ApplicabilityConditionNotMet {
                    condition: "collision_partition_reading_adequacy".to_owned(),
                    detail: format!(
                        "collision partition splits sources mapping to the same reading target `{tgt}` into distinct blocks ({prev} vs {label})"
                    ),
                });
            }
            vals.insert(tgt.to_owned(), label.clone());
        }
    }
    let mut target_law_values = BTreeMap::new();
    target_law_values.insert("law".to_owned(), vals);
    Ok(build_diagnostic_complex(nerve, &target_law_values))
}

fn fine_to_coarse_block_map(
    coarse: &[Vec<String>],
    fine: &[Vec<String>],
) -> Result<Vec<usize>, SilenceReason> {
    let coarse_sets: Vec<BTreeSet<&str>> = coarse
        .iter()
        .map(|b| b.iter().map(String::as_str).collect())
        .collect();
    let mut out = Vec::with_capacity(fine.len());
    for fb in fine {
        let Some(ci) = coarse_sets
            .iter()
            .position(|cb| fb.iter().all(|s| cb.contains(s.as_str())))
        else {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "partition_coarsening".to_owned(),
                detail: "fine partition block is not contained in any coarse block".to_owned(),
            });
        };
        out.push(ci);
    }
    Ok(out)
}

fn build_coarsening_map_matrices(
    coarse: &[Vec<String>],
    fine: &[Vec<String>],
    coarse_cpx: &DiagnosticComplexData,
    fine_cpx: &DiagnosticComplexData,
) -> Result<IntMatTriple, SilenceReason> {
    let f2c = fine_to_coarse_block_map(coarse, fine)?;
    let r0 = build_degree_restriction(&coarse_cpx.coords0, &fine_cpx.coords0, &f2c)?;
    let r1 = build_degree_restriction(&coarse_cpx.coords1, &fine_cpx.coords1, &f2c)?;
    let r2 = build_degree_restriction(&coarse_cpx.coords2, &fine_cpx.coords2, &f2c)?;
    Ok((r0, r1, r2))
}

fn parse_block_index(label: &str) -> Result<usize, SilenceReason> {
    label
        .strip_prefix('b')
        .and_then(|s| s.parse::<usize>().ok())
        .ok_or_else(|| SilenceReason::DiagnosticsStratificationOutOfScope {
            detail: format!("invalid internal partition block label `{label}`"),
        })
}

fn build_degree_restriction(
    coarse_coords: &[(usize, String, String)],
    fine_coords: &[(usize, String, String)],
    f2c: &[usize],
) -> Result<Vec<Vec<BigInt>>, SilenceReason> {
    let mut c_idx: BTreeMap<(usize, usize), usize> = BTreeMap::new();
    for (col, (cell, _, lbl)) in coarse_coords.iter().enumerate() {
        let bi = parse_block_index(lbl)?;
        c_idx.insert((*cell, bi), col);
    }
    let mut mat = vec![vec![BigInt::zero(); coarse_coords.len()]; fine_coords.len()];
    for (row, (cell, _, lbl)) in fine_coords.iter().enumerate() {
        let fbi = parse_block_index(lbl)?;
        let cbi = f2c[fbi];
        if let Some(&col) = c_idx.get(&(*cell, cbi)) {
            mat[row][col] = BigInt::one();
        }
    }
    Ok(mat)
}

/// 短完全列 `0 -> C^\bullet(coarse) --r--> C^\bullet(fine) --rho--> Q^\bullet -> 0` の
/// 余核複体 `Q` と全射 cochain 射 `rho` を構成する。
/// 二値合流では `Q` はちょうど `C^\bullet(K_a ∩ K_b)`、`(x, y) |-> y - x` と一致する（C3）。
fn build_cokernel_complex_and_rho(
    nerve: &ComputedNerve,
    coarse: &[Vec<String>],
    fine: &[Vec<String>],
    fine_cpx: &DiagnosticComplexData,
) -> Result<CokernelBundle, SilenceReason> {
    let f2c = fine_to_coarse_block_map(coarse, fine)?;

    // 各次数で (cell, coarse_block) ごとに存在する fine block の昇順リスト `[b_0, b_1, ..., b_{k-1}]`
    // を求め、k >= 2 のとき k-1 個の座標 `(cell, coarse_block, b_j - b_0)` (j = 1..k) を Q の基底とする。
    let (q_coords0, rho0, q0_lookup) = build_cokernel_degree(&fine_cpx.coords0, &f2c)?;
    let (q_coords1, rho1, q1_lookup) = build_cokernel_degree(&fine_cpx.coords1, &f2c)?;
    let (q_coords2, rho2, _) = build_cokernel_degree(&fine_cpx.coords2, &f2c)?;

    // Q 上の微分 d^0_Q, d^1_Q は rho ∘ d_fine = d_Q ∘ rho から一意に定まる。
    // 各 Q 座標 (cell, cbi, first_fb, fb) は fine 座標 (cell, fb) の像であり、
    // その微分は fine での微分を rho で送った結果そのもの。
    let mut d0_q = vec![vec![BigInt::zero(); q_coords0.len()]; q_coords1.len()];
    for (q_col, &(ci, cbi, _first_fb, fb)) in q_coords0.iter().enumerate() {
        // fine 基底元 e_{(ci, fb)} の d0_fine 像を rho1 で送る。
        for (ei, edge) in nerve.edges.iter().enumerate() {
            let sign = if edge.right_idx == ci && edge.left_idx == ci {
                BigInt::zero()
            } else if edge.right_idx == ci {
                BigInt::one()
            } else if edge.left_idx == ci {
                -BigInt::one()
            } else {
                continue;
            };
            if sign.is_zero() {
                continue;
            }
            if let Some(entries) = q1_lookup.get(&(ei, cbi)) {
                for &(q_row, e_first, e_fb) in entries {
                    if e_fb == fb {
                        d0_q[q_row][q_col] += &sign;
                    } else if e_first == fb {
                        d0_q[q_row][q_col] -= &sign;
                    }
                }
            }
        }
    }

    let mut d1_q = vec![vec![BigInt::zero(); q_coords1.len()]; q_coords2.len()];
    for (q_row, &(fi, cbi, f_first, f_fb)) in q_coords2.iter().enumerate() {
        let face = &nerve.faces[fi];
        let terms = [
            (face.e0_idx, BigInt::one()),
            (face.e1_idx, -BigInt::one()),
            (face.e2_idx, BigInt::one()),
        ];
        for (ei, sign) in terms {
            // Q 座標 (fi, cbi, f_first, f_fb) は fine 座標の差 e_{f_fb} - e_{f_first} を読む。
            // 辺 ei 上での e_{f_fb} - e_{f_first} を Q^1 基底で表す:
            //   (e_{f_fb} - e_{e_first}) - (e_{f_first} - e_{e_first})。
            if let Some(entries) = q1_lookup.get(&(ei, cbi)) {
                for &(q_col, e_first, e_fb) in entries {
                    if e_fb == f_fb {
                        d1_q[q_row][q_col] += &sign;
                    }
                    if e_fb == f_first {
                        d1_q[q_row][q_col] -= &sign;
                    }
                    let _ = e_first;
                }
            }
        }
    }
    let _ = q0_lookup;

    let q_data = DiagnosticComplexData {
        coords0: q_coords0
            .iter()
            .map(|&(c, cb, _, fb)| (c, format!("c{cb}"), format!("b{fb}")))
            .collect(),
        coords1: q_coords1
            .iter()
            .map(|&(c, cb, _, fb)| (c, format!("c{cb}"), format!("b{fb}")))
            .collect(),
        coords2: q_coords2
            .iter()
            .map(|&(c, cb, _, fb)| (c, format!("c{cb}"), format!("b{fb}")))
            .collect(),
        d0_z: d0_q,
        d1_z: d1_q,
    };
    Ok((q_data, rho0, rho1, rho2))
}

#[allow(clippy::type_complexity)]
fn build_cokernel_degree(
    fine_coords: &[(usize, String, String)],
    f2c: &[usize],
) -> Result<
    (
        Vec<(usize, usize, usize, usize)>,
        Vec<Vec<BigInt>>,
        BTreeMap<(usize, usize), Vec<(usize, usize, usize)>>,
    ),
    SilenceReason,
> {
    let mut grouped: BTreeMap<(usize, usize), Vec<(usize, usize)>> = BTreeMap::new();
    for (col, (cell, _, lbl)) in fine_coords.iter().enumerate() {
        let fbi = parse_block_index(lbl)?;
        let cbi = f2c[fbi];
        grouped.entry((*cell, cbi)).or_default().push((fbi, col));
    }

    let mut q_coords = Vec::new();
    let mut rho = Vec::new();
    let mut lookup: BTreeMap<(usize, usize), Vec<(usize, usize, usize)>> = BTreeMap::new();

    for ((cell, cbi), mut items) in grouped {
        items.sort_by_key(|&(fbi, _)| fbi);
        if items.len() < 2 {
            continue;
        }
        let (first_fb, first_col) = items[0];
        for &(fb, col) in &items[1..] {
            let q_row = q_coords.len();
            q_coords.push((cell, cbi, first_fb, fb));
            let mut row = vec![BigInt::zero(); fine_coords.len()];
            row[col] = BigInt::one();
            row[first_col] = -BigInt::one();
            rho.push(row);
            lookup
                .entry((cell, cbi))
                .or_default()
                .push((q_row, first_fb, fb));
        }
    }

    Ok((q_coords, rho, lookup))
}

/// D1–D2: 一般 `V(g_1, ..., g_r) ∩ D(h)` の標準 cycle + full 2-skeleton 構成と probe 検算。
pub(crate) fn compute_dimension_realization(
    dr: &DimensionRealizationSpec,
    diag_coeff: &CoeffDomain,
) -> Result<DimensionRealizationResult, SilenceReason> {
    let r = dr.vanishing_polys.len();
    let n = std::cmp::max(3, r + 1);

    // D1 標準 full 2-skeleton nerve を構築。
    let mut charts = Vec::with_capacity(n);
    for i in 0..n {
        let prev = (i + n - 1) % n;
        charts.push(ChartSupportSpec {
            name: format!("c{i}"),
            support: vec![format!("e{prev}"), format!("e{i}"), "s_star".to_owned()],
        });
    }
    let mut edges = Vec::new();
    for i in 0..n {
        for j in (i + 1)..n {
            edges.push(NerveEdgeSpec {
                name: format!("e_{i}_{j}"),
                left: format!("c{i}"),
                right: format!("c{j}"),
            });
        }
    }
    let mut faces = Vec::new();
    for i in 0..n {
        for j in (i + 1)..n {
            for k in (j + 1)..n {
                faces.push(NerveFaceSpec {
                    name: format!("f_{i}_{j}_{k}"),
                    e0: format!("e_{i}_{j}"),
                    e1: format!("e_{i}_{k}"),
                    e2: format!("e_{j}_{k}"),
                });
            }
        }
    }
    let nerve = compute_nerve(&SupportedNerveSpec {
        charts,
        edges,
        faces,
    })?;

    let (_, bindings) =
        ExprBindings::from_slices(&dr.base_vars, &[], &[]).map_err(map_diag_alg_err)?;
    let (_, empty_bindings) = ExprBindings::from_slices(&[], &[], &[]).map_err(map_diag_alg_err)?;

    let probe_results = match &dr.base_domain {
        CoeffDomain::Q => eval_dim_probes(
            dr,
            n,
            &nerve,
            diag_coeff,
            &bindings,
            &empty_bindings,
            &|e, b| Poly::from_expr_q(e, b),
        )?,
        CoeffDomain::Z => eval_dim_probes(
            dr,
            n,
            &nerve,
            diag_coeff,
            &bindings,
            &empty_bindings,
            &|e, b| Poly::from_expr_z(e, b),
        )?,
        CoeffDomain::Fp(p) => {
            if !archsig_common::prime::is_prime(p) {
                return Err(SilenceReason::UnsupportedCoeffRing {
                    domain: dr.base_domain.clone(),
                    detail: format!("base_domain modulus {p} is not prime"),
                });
            }
            let p1 = p.clone();
            eval_dim_probes(
                dr,
                n,
                &nerve,
                diag_coeff,
                &bindings,
                &empty_bindings,
                &move |e, b| Poly::from_expr_fp(e, b, &p1),
            )?
        }
    };

    let all_probes_matched = probe_results.iter().all(|p| p.matched);
    Ok(DimensionRealizationResult {
        cycle_vertices: n,
        probe_results,
        all_probes_matched,
    })
}

fn eval_dim_probes<C, FE>(
    dr: &DimensionRealizationSpec,
    n: usize,
    nerve: &ComputedNerve,
    diag_coeff: &CoeffDomain,
    bindings: &ExprBindings,
    empty_bindings: &ExprBindings,
    expand: &FE,
) -> Result<Vec<DimensionProbePointResult>, SilenceReason>
where
    C: RingCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
{
    let mut g_polys = Vec::with_capacity(dr.vanishing_polys.len());
    for g in &dr.vanishing_polys {
        g_polys.push(expand(&g.expr, bindings).map_err(map_diag_alg_err)?);
    }
    let h_poly = expand(&dr.invertible_poly.expr, bindings).map_err(map_diag_alg_err)?;

    let mut results = Vec::with_capacity(dr.probe_points.len());
    for pt in &dr.probe_points {
        let coord_map: BTreeMap<&str, &PolyExpr> =
            pt.coords.iter().map(|(v, e)| (v.as_str(), e)).collect();
        let mut pt_vals = Vec::with_capacity(dr.base_vars.len());
        for v in &dr.base_vars {
            let p = expand(coord_map[v.as_str()], empty_bindings).map_err(map_diag_alg_err)?;
            pt_vals.push(p.eval_at(&[]).map_err(map_diag_alg_err)?);
        }

        let mut g_vals = Vec::with_capacity(g_polys.len());
        for gp in &g_polys {
            g_vals.push(gp.eval_at(&pt_vals).map_err(map_diag_alg_err)?);
        }
        let h_val = h_poly.eval_at(&pt_vals).map_err(map_diag_alg_err)?;

        let all_g_zero = g_vals.iter().all(RingCoeff::coeff_is_zero);
        let h_nonzero = !h_val.coeff_is_zero();
        let expected_indicator = usize::from(all_g_zero && h_nonzero);

        // D1 割当て: e0 -> 0, e1 -> g_1, ..., e_r -> g_r, 残り -> 0, s_star -> h
        let zero_str = h_val.zero_like().to_string();
        let mut src_vals = BTreeMap::new();
        src_vals.insert("e0".to_owned(), zero_str.clone());
        for (i, gv) in g_vals.iter().enumerate() {
            src_vals.insert(format!("e{}", i + 1), gv.to_string());
        }
        for i in (g_vals.len() + 1)..n {
            src_vals.insert(format!("e{i}"), zero_str.clone());
        }
        src_vals.insert("s_star".to_owned(), h_val.to_string());

        let mut law_map = BTreeMap::new();
        law_map.insert("d1_law".to_owned(), src_vals);
        let cpx = build_diagnostic_complex(nerve, &law_map);
        let sum = evaluate_complex_over_domain(&cpx, diag_coeff)?;

        let matched = sum.h1_free_rank == expected_indicator && sum.h1_torsion.is_empty();
        results.push(DimensionProbePointResult {
            label: pt.label.clone(),
            expected_indicator,
            computed_h1_dim: sum.h1_free_rank,
            matched,
        });
    }
    Ok(results)
}
