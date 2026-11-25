//! Atlas 細分化（G-142 F1–F7・W3）:
//! Condition C0–C6 全 7 項目の独立検査・粗→細 cochain 比較 `(p^0, p^1)`・
//! `H^0/H^1` 同型・指定類保存・全修復 fiber 同型 `Φ_R` と逆復元・評価条件 `P ↪ T`・
//! 忘却 reading 反例（F7）。

use crate::algebra::cochain::{CochainComplex, CochainMap, mat_mul, mat_vec};
use crate::algebra::linear::smith_normal_form_z;
use crate::algebra::poly::{AlgebraError, Poly};
use crate::algebra::poly_expr::ExprBindings;
use crate::algebra::scalar::{FpElem, Rat, RingCoeff};
use crate::ir::atlas::{
    AtlasEvalConditionSpec, AtlasRefinementSpec, AtlasTaskSpec, ForgetfulReadingSpec,
};
use crate::ir::result::SilenceReason;
use crate::ir::result_phase4::{AtlasRefinementResult, ForgetfulReadingResult};
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::solver::atlas::{
    EvaluatedGraph, SpanningTreeData, apply_spanning_tree_phi, build_evaluated_graph,
    build_spanning_tree, eval_const_expr, is_graph_connected, map_atlas_alg_err,
};
use crate::solver::atlas_condition_c::check_condition_c0_to_c6;
use crate::solver::diagnostics::compute_nerve;
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::collections::{BTreeMap, BTreeSet};

type JointSolution<C> = (Option<Vec<C>>, Vec<Vec<C>>);

/// 粗/細 Atlas の細分化比較（Condition C0–C6・`p^0, p^1`・fiber 同型・F5・F7）を実行する。
#[allow(clippy::too_many_arguments)]
pub(crate) fn compute_atlas_refinement<C, FE, FLin>(
    spec: &AtlasTaskSpec,
    ref_spec: &AtlasRefinementSpec,
    coarse_graph: &EvaluatedGraph<C>,
    coarse_lambdas: &[C],
    _coarse_tree: &SpanningTreeData,
    _coarse_phi_r: &[C],
    empty_bindings: &ExprBindings,
    expand: &FE,
    solve_linear: &FLin,
) -> Result<AtlasRefinementResult, SilenceReason>
where
    C: RingCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
    FLin: Fn(&[Vec<C>], &[C], usize) -> Result<JointSolution<C>, SilenceReason>,
{
    if !is_graph_connected(&ref_spec.fine_vertices, &ref_spec.fine_edges) {
        return Err(SilenceReason::DisconnectedGraphOutOfScope {
            detail: format!(
                "fine graph in atlas refinement `{}` is disconnected",
                spec.name
            ),
        });
    }

    let fine_graph = build_evaluated_graph(
        &ref_spec.fine_vertices,
        &ref_spec.fine_edges,
        coarse_graph.zero.zero_like(),
        empty_bindings,
        expand,
    )?;

    // 1. Condition C0–C6 全 7 項目の独立検査（F4 / Lean `ConditionC` 厳密準拠）。
    let condition_c = check_condition_c0_to_c6(ref_spec)?;

    // 2. 粗→細 cochain 比較写像 p^0, p^1 と可換性 d_f^0 p^0 == p^1 d_c^0（F3）。
    let (p0, p1, p0_z, p1_z, v_map_idx, e_map_idx) =
        build_refinement_cochain_maps(ref_spec, coarse_graph, &fine_graph);
    let lhs = mat_mul(&fine_graph.d0, &p0, coarse_graph.vertices.len(), &coarse_graph.zero);
    let rhs = mat_mul(&p1, &coarse_graph.d0, coarse_graph.vertices.len(), &coarse_graph.zero);
    let cochain_map_commutes = lhs == rhs;

    // 3. H^0, H^1 同型判定（係数環 R 上で厳密判定: 体なら RREF、Z なら SNF）。
    let (h0_isomorphism, h1_isomorphism) = if cochain_map_commutes {
        check_graph_h0_h1_isomorphism(coarse_graph, &fine_graph, &p0_z, &p1_z, &spec.coeff_domain)?
    } else {
        (false, false)
    };

    // 4. 指定類保存 o_f = p^1 o_c, κ_f = p^1 κ_c（F3）。
    let fine_lambdas = mat_vec(&p0, coarse_lambdas, &coarse_graph.zero);
    let fine_d0_lam = mat_vec(&fine_graph.d0, &fine_lambdas, &coarse_graph.zero);
    let fine_residuals: Vec<C> = fine_d0_lam
        .iter()
        .zip(&fine_graph.offsets)
        .map(|(d, b)| d.sub_ref(b))
        .collect();
    let coarse_d0_lam = mat_vec(&coarse_graph.d0, coarse_lambdas, &coarse_graph.zero);
    let coarse_residuals: Vec<C> = coarse_d0_lam
        .iter()
        .zip(&coarse_graph.offsets)
        .map(|(d, b)| d.sub_ref(b))
        .collect();
    let pulled_residuals = mat_vec(&p1, &coarse_residuals, &coarse_graph.zero);
    let fine_tree = build_spanning_tree(&fine_graph);
    let diff_residuals: Vec<C> = fine_residuals
        .iter()
        .zip(&pulled_residuals)
        .map(|(a, b)| a.sub_ref(b))
        .collect();
    let phi_diff = apply_spanning_tree_phi(&fine_graph, &fine_tree, &diff_residuals);
    let designated_o_preserved =
        cochain_map_commutes && phi_diff.iter().all(RingCoeff::coeff_is_zero);
    let nerve_aligns_with_graph = check_nerve_aligns_with_graph(ref_spec, coarse_graph, &fine_graph)?;
    let designated_kappa_preserved =
        designated_o_preserved && condition_c.all_passed && nerve_aligns_with_graph;

    // 5. 全修復 fiber 同型 Φ_R: F_c(R) -> F_f(R) と逆復元（F2・F5）。
    let (repair_fiber_iso, inverse_recon_ok, eval_cond_preserved) = verify_repair_fiber_iso(
        spec,
        ref_spec,
        coarse_graph,
        &fine_graph,
        coarse_lambdas,
        &fine_lambdas,
        &v_map_idx,
        &e_map_idx,
        &p0,
        &p1,
        expand,
        solve_linear,
    )?;

    // 6. 情報を落とす reading の反例比較（F7）。
    let forgetful_reading_contrast = if let Some(fg) = &ref_spec.forgetful_reading {
        Some(evaluate_forgetful_reading(
            fg,
            condition_c.all_passed,
            empty_bindings,
            expand,
        )?)
    } else {
        None
    };

    Ok(AtlasRefinementResult {
        condition_c,
        cochain_map_commutes,
        h0_isomorphism,
        h1_isomorphism,
        designated_o_preserved,
        designated_kappa_preserved,
        repair_fiber_isomorphism_verified: repair_fiber_iso,
        inverse_reconstruction_verified: inverse_recon_ok,
        eval_condition_fiber_preserved: eval_cond_preserved,
        forgetful_reading_contrast,
    })
}

/// G-142 E3 整合検査: 粗/細の診断 nerve と nerve 射が粗/細グラフおよび `vertex_map`/`edge_map` と
/// 1 対 1 に対応し、全 chart・全 edge の支持が非空かつ face が空であることを独立検証する。
fn check_nerve_aligns_with_graph<C: RingCoeff>(
    ref_spec: &AtlasRefinementSpec,
    coarse_graph: &EvaluatedGraph<C>,
    fine_graph: &EvaluatedGraph<C>,
) -> Result<bool, SilenceReason> {
    let coarse_nerve = compute_nerve(&ref_spec.coarse_nerve)?;
    let fine_nerve = compute_nerve(&ref_spec.fine_nerve)?;

    let single_matches = |nerve_spec: &crate::ir::diagnostics::SupportedNerveSpec,
                          computed: &crate::solver::diagnostics::ComputedNerve,
                          graph: &EvaluatedGraph<C>|
     -> bool {
        if !nerve_spec.faces.is_empty() {
            return false;
        }
        if nerve_spec.charts.len() != graph.vertices.len()
            || nerve_spec.edges.len() != graph.edges.len()
        {
            return false;
        }
        let g_verts: BTreeSet<&str> = graph.vertices.iter().map(String::as_str).collect();
        let n_charts: BTreeSet<&str> = nerve_spec.charts.iter().map(|c| c.name.as_str()).collect();
        if g_verts != n_charts {
            return false;
        }
        if computed.chart_supports.iter().any(BTreeSet::is_empty)
            || computed.edges.iter().any(|e| e.support.is_empty())
        {
            return false;
        }
        let g_edges: BTreeMap<&str, (&str, &str)> = graph
            .edges
            .iter()
            .map(|e| {
                (
                    e.name.as_str(),
                    (
                        graph.vertices[e.from].as_str(),
                        graph.vertices[e.to].as_str(),
                    ),
                )
            })
            .collect();
        for ne in &nerve_spec.edges {
            match g_edges.get(ne.name.as_str()) {
                Some(&(gf, gt)) if gf == ne.left.as_str() && gt == ne.right.as_str() => {}
                _ => return false,
            }
        }
        true
    };

    if !single_matches(&ref_spec.coarse_nerve, &coarse_nerve, coarse_graph)
        || !single_matches(&ref_spec.fine_nerve, &fine_nerve, fine_graph)
    {
        return Ok(false);
    }

    let vm: BTreeMap<&str, &str> = ref_spec
        .vertex_map
        .iter()
        .map(|(f, c)| (f.as_str(), c.as_str()))
        .collect();
    let ncm: BTreeMap<&str, &str> = ref_spec
        .nerve_chart_map
        .iter()
        .map(|(f, c)| (f.as_str(), c.as_str()))
        .collect();
    if vm != ncm {
        return Ok(false);
    }

    let em: BTreeMap<&str, Option<&str>> = ref_spec
        .edge_map
        .iter()
        .map(|(f, c)| (f.as_str(), c.as_deref()))
        .collect();
    let nem: BTreeMap<&str, Option<&str>> = ref_spec
        .nerve_edge_map
        .iter()
        .map(|(f, c)| (f.as_str(), c.as_deref()))
        .collect();
    Ok(em == nem)
}

#[allow(clippy::type_complexity)]
fn build_refinement_cochain_maps<C: RingCoeff>(
    ref_spec: &AtlasRefinementSpec,
    coarse: &EvaluatedGraph<C>,
    fine: &EvaluatedGraph<C>,
) -> (
    Vec<Vec<C>>,
    Vec<Vec<C>>,
    Vec<Vec<BigInt>>,
    Vec<Vec<BigInt>>,
    Vec<usize>,
    Vec<Option<(usize, i8)>>,
) {
    let one = coarse.zero.one_like();
    let neg_one = coarse.zero.sub_ref(&one);
    let mut v_map = vec![0usize; fine.vertices.len()];
    for (fv, cv) in &ref_spec.vertex_map {
        v_map[fine.v_idx[fv]] = coarse.v_idx[cv];
    }
    let mut p0 = vec![vec![coarse.zero.zero_like(); coarse.vertices.len()]; fine.vertices.len()];
    let mut p0_z = vec![vec![BigInt::zero(); coarse.vertices.len()]; fine.vertices.len()];
    for (fi, &ci) in v_map.iter().enumerate() {
        p0[fi][ci] = one.clone();
        p0_z[fi][ci] = BigInt::one();
    }

    let mut e_map: Vec<Option<(usize, i8)>> = vec![None; fine.edges.len()];
    let mut p1 = vec![vec![coarse.zero.zero_like(); coarse.edges.len()]; fine.edges.len()];
    let mut p1_z = vec![vec![BigInt::zero(); coarse.edges.len()]; fine.edges.len()];
    for (fe_name, ce_opt) in &ref_spec.edge_map {
        let fi = fine.e_idx[fe_name];
        if let Some(ce_name) = ce_opt {
            let ci = coarse.e_idx[ce_name];
            let fe = &fine.edges[fi];
            let ce = &coarse.edges[ci];
            let (sign_c, sign_z, s) = if v_map[fe.from] == ce.from && v_map[fe.to] == ce.to {
                (one.clone(), BigInt::one(), 1i8)
            } else if v_map[fe.from] == ce.to && v_map[fe.to] == ce.from {
                (neg_one.clone(), -BigInt::one(), -1i8)
            } else {
                (one.clone(), BigInt::one(), 1i8)
            };
            p1[fi][ci] = sign_c;
            p1_z[fi][ci] = sign_z;
            e_map[fi] = Some((ci, s));
        }
    }

    (p0, p1, p0_z, p1_z, v_map, e_map)
}

fn check_graph_h0_h1_isomorphism<C: RingCoeff>(
    coarse: &EvaluatedGraph<C>,
    fine: &EvaluatedGraph<C>,
    p0_z: &[Vec<BigInt>],
    p1_z: &[Vec<BigInt>],
    coeff_domain: &CoeffDomain,
) -> Result<(bool, bool), SilenceReason> {
    let d0_c_z = graph_d0_z(coarse);
    let d0_f_z = graph_d0_z(fine);
    match coeff_domain {
        CoeffDomain::Q => {
            let cpx_c = CochainComplex::new(
                coarse.vertices.len(),
                coarse.edges.len(),
                0,
                lift_z_to_q(&d0_c_z),
                Vec::new(),
                Rat::zero(),
            )
            .map_err(map_atlas_alg_err)?;
            let cpx_f = CochainComplex::new(
                fine.vertices.len(),
                fine.edges.len(),
                0,
                lift_z_to_q(&d0_f_z),
                Vec::new(),
                Rat::zero(),
            )
            .map_err(map_atlas_alg_err)?;
            let map = CochainMap::new(
                &cpx_c,
                &cpx_f,
                lift_z_to_q(p0_z),
                lift_z_to_q(p1_z),
                Vec::new(),
            )
            .map_err(map_atlas_alg_err)?;
            let ind = map.induced_field(&cpx_c, &cpx_f).map_err(map_atlas_alg_err)?;
            Ok((ind.h0.isomorphism, ind.h1.isomorphism))
        }
        CoeffDomain::Fp(p) => {
            let zero_fp = FpElem::from_checked_prime(BigInt::zero(), p.clone());
            let cpx_c = CochainComplex::new(
                coarse.vertices.len(),
                coarse.edges.len(),
                0,
                lift_z_to_fp(&d0_c_z, p),
                Vec::new(),
                zero_fp.clone(),
            )
            .map_err(map_atlas_alg_err)?;
            let cpx_f = CochainComplex::new(
                fine.vertices.len(),
                fine.edges.len(),
                0,
                lift_z_to_fp(&d0_f_z, p),
                Vec::new(),
                zero_fp,
            )
            .map_err(map_atlas_alg_err)?;
            let map = CochainMap::new(
                &cpx_c,
                &cpx_f,
                lift_z_to_fp(p0_z, p),
                lift_z_to_fp(p1_z, p),
                Vec::new(),
            )
            .map_err(map_atlas_alg_err)?;
            let ind = map.induced_field(&cpx_c, &cpx_f).map_err(map_atlas_alg_err)?;
            Ok((ind.h0.isomorphism, ind.h1.isomorphism))
        }
        CoeffDomain::Z => {
            let c_z_g = graph_as_z(coarse);
            let f_z_g = graph_as_z(fine);
            let t_c = build_spanning_tree(&c_z_g);
            let t_f = build_spanning_tree(&f_z_g);
            let r_c = t_c.chord_edge_indices.len();
            let r_f = t_f.chord_edge_indices.len();
            let h0_iso = {
                let ones_c = vec![BigInt::one(); coarse.vertices.len()];
                let img = mat_vec(p0_z, &ones_c, &BigInt::zero());
                img.iter().all(|v| *v == BigInt::one())
            };
            if r_c != r_f {
                return Ok((h0_iso, false));
            }
            if r_c == 0 {
                return Ok((h0_iso, true));
            }
            let mut mat = vec![vec![BigInt::zero(); r_c]; r_f];
            for (col, &c_ei) in t_c.chord_edge_indices.iter().enumerate() {
                let mut e_vec = vec![BigInt::zero(); coarse.edges.len()];
                e_vec[c_ei] = BigInt::one();
                let img = mat_vec(p1_z, &e_vec, &BigInt::zero());
                let coords = apply_spanning_tree_phi(&f_z_g, &t_f, &img);
                for (row, val) in coords.into_iter().enumerate() {
                    mat[row][col] = val;
                }
            }
            let snf = smith_normal_form_z(&mat, r_c).map_err(map_atlas_alg_err)?;
            let h1_iso = snf.rank == r_c && snf.diagonals.iter().all(|d| *d == BigInt::one());
            Ok((h0_iso, h1_iso))
        }
    }
}

/// F2 / F5: 全修復 fiber `F_c(R)` と `F_f(R)` の間の `Φ_R` 同型・逆復元・評価条件 `P ↪ T` 保存を検算する。
#[allow(clippy::too_many_arguments)]
fn verify_repair_fiber_iso<C, FE, FLin>(
    spec: &AtlasTaskSpec,
    ref_spec: &AtlasRefinementSpec,
    coarse: &EvaluatedGraph<C>,
    fine: &EvaluatedGraph<C>,
    coarse_lambdas: &[C],
    fine_lambdas: &[C],
    v_map: &[usize],
    e_map: &[Option<(usize, i8)>],
    p0: &[Vec<C>],
    p1: &[Vec<C>],
    expand: &FE,
    solve_linear: &FLin,
) -> Result<(bool, bool, Option<bool>), SilenceReason>
where
    C: RingCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
    FLin: Fn(&[Vec<C>], &[C], usize) -> Result<JointSolution<C>, SilenceReason>,
{
    let allowed_vc: BTreeSet<usize> = spec
        .allowed_vertices
        .iter()
        .map(|v| coarse.v_idx[v])
        .collect();
    let allowed_ec: BTreeSet<usize> = spec
        .allowed_edges
        .iter()
        .map(|e| coarse.e_idx[e])
        .collect();

    let fine_av: Vec<usize> = (0..fine.vertices.len())
        .filter(|&fv| allowed_vc.contains(&v_map[fv]))
        .collect();
    let fine_ae: Vec<usize> = (0..fine.edges.len())
        .filter(|&fe| e_map[fe].is_some_and(|(ce, _)| allowed_ec.contains(&ce)))
        .collect();
    let coarse_av: Vec<usize> = spec
        .allowed_vertices
        .iter()
        .map(|v| coarse.v_idx[v])
        .collect();
    let coarse_ae: Vec<usize> = spec
        .allowed_edges
        .iter()
        .map(|e| coarse.e_idx[e])
        .collect();

    let (c_part, c_ker) = solve_joint_repair(coarse, coarse_lambdas, &coarse_av, &coarse_ae, solve_linear)?;
    let (f_part, f_ker) = solve_joint_repair(fine, fine_lambdas, &fine_av, &fine_ae, solve_linear)?;

    let mut iso_ok = c_part.is_some() == f_part.is_some() && c_ker.len() == f_ker.len();
    let mut inv_ok = iso_ok;

    let check_forward = |vec_c: &(Vec<C>, Vec<C>), is_hom: bool| -> bool {
        let af = mat_vec(p0, &vec_c.0, &coarse.zero);
        let dbf = mat_vec(p1, &vec_c.1, &coarse.zero);
        let lhs = mat_vec(&fine.d0, &af, &coarse.zero);
        let target: Vec<C> = if is_hom {
            dbf
        } else {
            let f_d0_l = mat_vec(&fine.d0, fine_lambdas, &coarse.zero);
            fine.offsets
                .iter()
                .zip(&f_d0_l)
                .zip(&dbf)
                .map(|((b, dl), db)| b.sub_ref(dl).add_ref(db))
                .collect()
        };
        lhs == target
    };

    let try_inverse = |vec_f: &(Vec<C>, Vec<C>)| -> Option<(Vec<C>, Vec<C>)> {
        let mut ac: Vec<Option<C>> = vec![None; coarse.vertices.len()];
        for (fv, &cv) in v_map.iter().enumerate() {
            let val = &vec_f.0[fv];
            if let Some(prev) = &ac[cv] {
                if prev != val {
                    return None;
                }
            } else {
                ac[cv] = Some(val.clone());
            }
        }
        let ac_vec: Vec<C> = ac.into_iter().collect::<Option<Vec<C>>>()?;
        let mut dbc: Vec<Option<C>> = vec![None; coarse.edges.len()];
        for (fe, map_opt) in e_map.iter().enumerate() {
            let val = &vec_f.1[fe];
            match map_opt {
                None => {
                    if !val.coeff_is_zero() {
                        return None;
                    }
                }
                Some((ce, s)) => {
                    let signed = if *s < 0 {
                        coarse.zero.sub_ref(val)
                    } else {
                        val.clone()
                    };
                    if let Some(prev) = &dbc[*ce] {
                        if prev != &signed {
                            return None;
                        }
                    } else {
                        dbc[*ce] = Some(signed);
                    }
                }
            }
        }
        let dbc_vec: Vec<C> = dbc
            .into_iter()
            .map(|o| o.unwrap_or_else(|| coarse.zero.zero_like()))
            .collect();
        Some((ac_vec, dbc_vec))
    };

    let check_coarse = |vec_c: &(Vec<C>, Vec<C>), is_hom: bool| -> bool {
        let lhs = mat_vec(&coarse.d0, &vec_c.0, &coarse.zero);
        let target: Vec<C> = if is_hom {
            vec_c.1.clone()
        } else {
            let c_d0_l = mat_vec(&coarse.d0, coarse_lambdas, &coarse.zero);
            coarse
                .offsets
                .iter()
                .zip(&c_d0_l)
                .zip(&vec_c.1)
                .map(|((b, dl), db)| b.sub_ref(dl).add_ref(db))
                .collect()
        };
        lhs == target
    };

    if let (Some(cp), Some(fp)) = (&c_part, &f_part) {
        if !check_forward(cp, false) {
            iso_ok = false;
        }
        let phi_cp = (
            mat_vec(p0, &cp.0, &coarse.zero),
            mat_vec(p1, &cp.1, &coarse.zero),
        );
        if try_inverse(&phi_cp).as_ref() != Some(cp) {
            inv_ok = false;
        }
        if let Some(psi_fp) = try_inverse(fp) {
            let back = (
                mat_vec(p0, &psi_fp.0, &coarse.zero),
                mat_vec(p1, &psi_fp.1, &coarse.zero),
            );
            if back != *fp || !check_forward(&psi_fp, false) || !check_coarse(&psi_fp, false) {
                inv_ok = false;
            }
        } else {
            inv_ok = false;
        }
    }

    for ck in &c_ker {
        if !check_forward(ck, true) {
            iso_ok = false;
        }
        let phi_ck = (
            mat_vec(p0, &ck.0, &coarse.zero),
            mat_vec(p1, &ck.1, &coarse.zero),
        );
        if try_inverse(&phi_ck).as_ref() != Some(ck) {
            inv_ok = false;
        }
    }
    for fk in &f_ker {
        if let Some(psi_fk) = try_inverse(fk) {
            let back = (
                mat_vec(p0, &psi_fk.0, &coarse.zero),
                mat_vec(p1, &psi_fk.1, &coarse.zero),
            );
            if back != *fk || !check_forward(&psi_fk, true) || !check_coarse(&psi_fk, true) {
                inv_ok = false;
            }
        } else {
            inv_ok = false;
        }
    }

    let eval_cond_preserved = if let Some(ec) = &ref_spec.eval_condition {
        Some(verify_eval_condition_f5(
            ec,
            &spec.coeff_domain,
            coarse,
            coarse_lambdas,
            &c_part,
            &c_ker,
            &f_part,
            p0,
            p1,
            &try_inverse,
            iso_ok && inv_ok,
            expand,
        )?)
    } else {
        None
    };

    Ok((iso_ok && inv_ok, inv_ok, eval_cond_preserved))
}

#[allow(clippy::too_many_arguments, clippy::type_complexity)]
fn verify_eval_condition_f5<C, FE, FInv>(
    ec: &AtlasEvalConditionSpec,
    coeff_domain: &CoeffDomain,
    coarse: &EvaluatedGraph<C>,
    coarse_lambdas: &[C],
    c_part: &Option<(Vec<C>, Vec<C>)>,
    c_ker: &[(Vec<C>, Vec<C>)],
    f_part: &Option<(Vec<C>, Vec<C>)>,
    p0: &[Vec<C>],
    p1: &[Vec<C>],
    try_inverse: &FInv,
    fiber_iso_ok: bool,
    expand: &FE,
) -> Result<bool, SilenceReason>
where
    C: RingCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
    FInv: Fn(&(Vec<C>, Vec<C>)) -> Option<(Vec<C>, Vec<C>)>,
{
    let mut all_vars = coarse.vertices.clone();
    all_vars.extend(coarse.edges.iter().map(|e| e.name.clone()));
    let (_, bindings) =
        ExprBindings::from_slices(&all_vars, &[], &[]).map_err(map_atlas_alg_err)?;

    let mut eval_polys = Vec::with_capacity(ec.evaluations.len());
    for item in &ec.evaluations {
        eval_polys.push(expand(&item.expr, &bindings).map_err(map_atlas_alg_err)?);
    }
    let mut eq_polys = Vec::with_capacity(ec.equations.len());
    for item in &ec.equations {
        eq_polys.push(expand(&item.expr, &bindings).map_err(map_atlas_alg_err)?);
    }
    let mut inv_polys = Vec::with_capacity(ec.invertibles.len());
    for item in &ec.invertibles {
        inv_polys.push(expand(&item.expr, &bindings).map_err(map_atlas_alg_err)?);
    }

    if !fiber_iso_ok {
        return Ok(false);
    }

    let one = coarse.zero.one_like();
    let neg_one = coarse.zero.sub_ref(&one);
    let is_unit = |val: &C| -> bool {
        match coeff_domain {
            CoeffDomain::Z => *val == one || *val == neg_one,
            CoeffDomain::Q | CoeffDomain::Fp(_) => !val.coeff_is_zero(),
        }
    };

    let eval_tuple = |sol: &(Vec<C>, Vec<C>)| -> Result<(Vec<C>, bool), SilenceReason> {
        let mut pt = Vec::with_capacity(all_vars.len());
        for (l, a) in coarse_lambdas.iter().zip(&sol.0) {
            pt.push(l.add_ref(a));
        }
        for (b, db) in coarse.offsets.iter().zip(&sol.1) {
            pt.push(b.add_ref(db));
        }
        let mut vals = Vec::with_capacity(eval_polys.len());
        for ep in &eval_polys {
            vals.push(ep.eval_at(&pt).map_err(map_atlas_alg_err)?);
        }
        let mut cond_ok = true;
        for eqp in &eq_polys {
            if !eqp.eval_at(&pt).map_err(map_atlas_alg_err)?.coeff_is_zero() {
                cond_ok = false;
            }
        }
        for invp in &inv_polys {
            if !is_unit(&invp.eval_at(&pt).map_err(map_atlas_alg_err)?) {
                cond_ok = false;
            }
        }
        Ok((vals, cond_ok))
    };

    if let (Some(cp), Some(fp)) = (c_part, f_part) {
        let c_ev = eval_tuple(cp)?;
        let phi_cp = (
            mat_vec(p0, &cp.0, &coarse.zero),
            mat_vec(p1, &cp.1, &coarse.zero),
        );
        let Some(back_cp) = try_inverse(&phi_cp) else {
            return Ok(false);
        };
        if eval_tuple(&back_cp)? != c_ev {
            return Ok(false);
        }
        let Some(psi_fp) = try_inverse(fp) else {
            return Ok(false);
        };
        let phi_psi_fp = (
            mat_vec(p0, &psi_fp.0, &coarse.zero),
            mat_vec(p1, &psi_fp.1, &coarse.zero),
        );
        if phi_psi_fp != *fp {
            return Ok(false);
        }
        let _ = eval_tuple(&psi_fp)?;
        for ck in c_ker {
            let shifted = (
                cp.0.iter().zip(&ck.0).map(|(a, b)| a.add_ref(b)).collect(),
                cp.1.iter().zip(&ck.1).map(|(a, b)| a.add_ref(b)).collect(),
            );
            let s_ev = eval_tuple(&shifted)?;
            let phi_s = (
                mat_vec(p0, &shifted.0, &coarse.zero),
                mat_vec(p1, &shifted.1, &coarse.zero),
            );
            let Some(back_s) = try_inverse(&phi_s) else {
                return Ok(false);
            };
            if eval_tuple(&back_s)? != s_ev {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

#[allow(clippy::type_complexity)]
fn solve_joint_repair<C, FLin>(
    graph: &EvaluatedGraph<C>,
    lambdas: &[C],
    allowed_v: &[usize],
    allowed_e: &[usize],
    solve_linear: &FLin,
) -> Result<(Option<(Vec<C>, Vec<C>)>, Vec<(Vec<C>, Vec<C>)>), SilenceReason>
where
    C: RingCoeff,
    FLin: Fn(&[Vec<C>], &[C], usize) -> Result<JointSolution<C>, SilenceReason>,
{
    let nv = allowed_v.len();
    let ne = allowed_e.len();
    let total = nv + ne;
    let d0_lam = mat_vec(&graph.d0, lambdas, &graph.zero);
    let rhs: Vec<C> = graph
        .offsets
        .iter()
        .zip(&d0_lam)
        .map(|(b, dl)| b.sub_ref(dl))
        .collect();

    let one = graph.zero.one_like();
    let neg_one = graph.zero.sub_ref(&one);
    let mut mat = vec![vec![graph.zero.zero_like(); total]; graph.edges.len()];
    for (col, &vi) in allowed_v.iter().enumerate() {
        for (row, drow) in graph.d0.iter().enumerate() {
            mat[row][col] = drow[vi].clone();
        }
    }
    for (col, &ei) in allowed_e.iter().enumerate() {
        mat[ei][nv + col] = neg_one.clone();
    }

    let unpack = |sol: &[C]| -> (Vec<C>, Vec<C>) {
        let mut a = vec![graph.zero.zero_like(); graph.vertices.len()];
        for (i, &vi) in allowed_v.iter().enumerate() {
            a[vi] = sol[i].clone();
        }
        let mut db = vec![graph.zero.zero_like(); graph.edges.len()];
        for (i, &ei) in allowed_e.iter().enumerate() {
            db[ei] = sol[nv + i].clone();
        }
        (a, db)
    };

    let (part_opt, ker_vecs) = solve_linear(&mat, &rhs, total)?;
    Ok((
        part_opt.map(|p| unpack(&p)),
        ker_vecs.iter().map(|v| unpack(v)).collect(),
    ))
}

/// F7: adequacy + C0–C6 成立下で、忘却変数 `t` に対する評価と条件の fiber 一定性・降下可否を判定する。
fn evaluate_forgetful_reading<C, FE>(
    fg: &ForgetfulReadingSpec,
    adequacy_and_c0_c6_hold: bool,
    empty_bindings: &ExprBindings,
    expand: &FE,
) -> Result<ForgetfulReadingResult, SilenceReason>
where
    C: RingCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
{
    let (_, fg_bindings) =
        ExprBindings::from_slices(std::slice::from_ref(&fg.forgotten_var), &[], &[])
            .map_err(map_atlas_alg_err)?;
    let eval_poly = expand(&fg.eval_expr, &fg_bindings).map_err(map_atlas_alg_err)?;
    let cond_poly = expand(&fg.condition_eq, &fg_bindings).map_err(map_atlas_alg_err)?;

    let mut sample_eval_values = BTreeMap::new();
    let mut sample_condition_holds = BTreeMap::new();
    let mut eval_set = BTreeSet::new();
    let mut cond_set = BTreeSet::new();

    for sv in &fg.sample_values {
        let v = eval_const_expr(sv, empty_bindings, expand)?;
        let ev = eval_poly
            .eval_at(std::slice::from_ref(&v))
            .map_err(map_atlas_alg_err)?;
        let cv = cond_poly
            .eval_at(std::slice::from_ref(&v))
            .map_err(map_atlas_alg_err)?;
        let holds = cv.coeff_is_zero();
        let key = v.to_string();
        let ev_str = ev.to_string();
        eval_set.insert(ev_str.clone());
        cond_set.insert(holds);
        sample_eval_values.insert(key.clone(), ev_str);
        sample_condition_holds.insert(key, holds);
    }

    let eval_constant_on_fiber = eval_poly.is_constant() && eval_set.len() <= 1;
    let condition_constant_on_fiber = cond_poly.is_constant() && cond_set.len() <= 1;

    Ok(ForgetfulReadingResult {
        adequacy_and_c0_c6_hold,
        eval_constant_on_fiber,
        eval_descends_to_coarse: eval_constant_on_fiber,
        condition_constant_on_fiber,
        condition_descends_to_coarse: condition_constant_on_fiber,
        sample_eval_values,
        sample_condition_holds,
    })
}

fn graph_d0_z<C: RingCoeff>(graph: &EvaluatedGraph<C>) -> Vec<Vec<BigInt>> {
    let mut d0 = vec![vec![BigInt::zero(); graph.vertices.len()]; graph.edges.len()];
    for (ei, e) in graph.edges.iter().enumerate() {
        d0[ei][e.to] = BigInt::one();
        d0[ei][e.from] = -BigInt::one();
    }
    d0
}

fn graph_as_z<C: RingCoeff>(graph: &EvaluatedGraph<C>) -> EvaluatedGraph<BigInt> {
    let d0 = graph_d0_z(graph);
    let edges = graph
        .edges
        .iter()
        .map(|e| crate::solver::atlas::EvaluatedEdge {
            name: e.name.clone(),
            from: e.from,
            to: e.to,
        })
        .collect();
    EvaluatedGraph {
        vertices: graph.vertices.clone(),
        v_idx: graph.v_idx.clone(),
        edges,
        e_idx: graph.e_idx.clone(),
        d0,
        offsets: vec![BigInt::zero(); graph.edges.len()],
        zero: BigInt::zero(),
    }
}

fn lift_z_to_q(mat: &[Vec<BigInt>]) -> Vec<Vec<Rat>> {
    mat.iter()
        .map(|r| r.iter().map(|v| Rat::from_int(v.clone())).collect())
        .collect()
}

fn lift_z_to_fp(mat: &[Vec<BigInt>], p: &num_bigint::BigUint) -> Vec<Vec<FpElem>> {
    mat.iter()
        .map(|r| {
            r.iter()
                .map(|v| FpElem::from_checked_prime(v.clone(), p.clone()))
                .collect()
        })
        .collect()
}
