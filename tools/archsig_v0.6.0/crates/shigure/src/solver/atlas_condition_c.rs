//! Atlas 細分化の Condition C0–C6 全 7 項目独立検査（G-142 F4 / Lean `ConditionC` 厳密準拠）。

use crate::algebra::artin::{AffineSolutionField, solve_affine_field};
use crate::algebra::scalar::Rat;
use crate::ir::atlas::AtlasRefinementSpec;
use crate::ir::result::SilenceReason;
use crate::ir::result_phase4::ConditionCResult;
use crate::solver::atlas::map_atlas_alg_err;
use crate::solver::diagnostics::{ComputedNerve, compute_nerve};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

/// Lean `ResolutionInvarianceConditions.lean` の Condition C0–C6 全 7 項目を独立に実検査する。
pub(crate) fn check_condition_c0_to_c6(
    ref_spec: &AtlasRefinementSpec,
) -> Result<ConditionCResult, SilenceReason> {
    let coarse_nerve = compute_nerve(&ref_spec.coarse_nerve)?;
    let fine_nerve = compute_nerve(&ref_spec.fine_nerve)?;

    let q_c: BTreeMap<&str, &str> = ref_spec
        .coarse_reading
        .iter()
        .map(|(s, t)| (s.as_str(), t.as_str()))
        .collect();
    let q_f: BTreeMap<&str, &str> = ref_spec
        .fine_reading
        .iter()
        .map(|(s, t)| (s.as_str(), t.as_str()))
        .collect();

    // 比較 factor ψ: T_f -> T_c の well-defined 性（coarseReading.CoarserThan fineReading）。
    let mut psi: BTreeMap<&str, &str> = BTreeMap::new();
    let mut factor_valid = true;
    for s in &ref_spec.common_sources {
        let tf = q_f[s.as_str()];
        let tc = q_c[s.as_str()];
        if let Some(&prev) = psi.get(tf) {
            if prev != tc {
                factor_valid = false;
            }
        } else {
            psi.insert(tf, tc);
        }
    }

    let c_chart_idx: BTreeMap<&str, usize> = ref_spec
        .coarse_nerve
        .charts
        .iter()
        .enumerate()
        .map(|(i, c)| (c.name.as_str(), i))
        .collect();
    let f_chart_idx: BTreeMap<&str, usize> = ref_spec
        .fine_nerve
        .charts
        .iter()
        .enumerate()
        .map(|(i, c)| (c.name.as_str(), i))
        .collect();
    let c_edge_idx: BTreeMap<&str, usize> = ref_spec
        .coarse_nerve
        .edges
        .iter()
        .enumerate()
        .map(|(i, e)| (e.name.as_str(), i))
        .collect();
    let f_edge_idx: BTreeMap<&str, usize> = ref_spec
        .fine_nerve
        .edges
        .iter()
        .enumerate()
        .map(|(i, e)| (e.name.as_str(), i))
        .collect();
    let c_face_idx: BTreeMap<&str, usize> = ref_spec
        .coarse_nerve
        .faces
        .iter()
        .enumerate()
        .map(|(i, f)| (f.name.as_str(), i))
        .collect();
    let f_face_idx: BTreeMap<&str, usize> = ref_spec
        .fine_nerve
        .faces
        .iter()
        .enumerate()
        .map(|(i, f)| (f.name.as_str(), i))
        .collect();

    let mut chart_map = vec![0usize; fine_nerve.chart_names.len()];
    for (fc, cc) in &ref_spec.nerve_chart_map {
        chart_map[f_chart_idx[fc.as_str()]] = c_chart_idx[cc.as_str()];
    }
    let mut edge_map: Vec<Option<usize>> = vec![None; fine_nerve.edges.len()];
    for (fe, ce_opt) in &ref_spec.nerve_edge_map {
        edge_map[f_edge_idx[fe.as_str()]] = ce_opt.as_ref().map(|ce| c_edge_idx[ce.as_str()]);
    }
    let mut face_map: Vec<Option<usize>> = vec![None; fine_nerve.faces.len()];
    for (ff, cf_opt) in &ref_spec.nerve_face_map {
        face_map[f_face_idx[ff.as_str()]] = cf_opt.as_ref().map(|cf| c_face_idx[cf.as_str()]);
    }

    // C0: 各粗 chart の支持は、その fiber 内の細 chart 支持の ψ 像の和集合とちょうど等しい。
    let c0_support_image = if !factor_valid {
        false
    } else {
        let mut ok = true;
        for (fi, f_sup) in fine_nerve.chart_supports.iter().enumerate() {
            let ci = chart_map[fi];
            for t in f_sup {
                match psi.get(t.as_str()) {
                    Some(&tc) if coarse_nerve.chart_supports[ci].contains(tc) => {}
                    _ => {
                        ok = false;
                    }
                }
            }
        }
        for (ci, c_sup) in coarse_nerve.chart_supports.iter().enumerate() {
            let mut img_union: BTreeSet<String> = BTreeSet::new();
            for (fi, &mapped_ci) in chart_map.iter().enumerate() {
                if mapped_ci == ci {
                    for t in &fine_nerve.chart_supports[fi] {
                        if let Some(&tc) = psi.get(t.as_str()) {
                            img_union.insert(tc.to_owned());
                        }
                    }
                }
            }
            if img_union != *c_sup {
                ok = false;
            }
        }
        ok
    };

    // C1: 各非空粗 chart fiber は非空かつ、両端がその fiber に入る細辺（CoordinateFiberEdge）で連結。
    let c1_block_fiber_connected = check_c1_fiber_connected(&coarse_nerve, &fine_nerve, &chart_map);

    // C2: 各非空粗 edge は、端点と非空支持が整合する細 edge lift を少なくとも 1 つ持つ。
    let mut c2_edge_lift = true;
    for (cei, ce) in coarse_nerve.edges.iter().enumerate() {
        if ce.support.is_empty() {
            continue;
        }
        let has_lift = fine_nerve.edges.iter().enumerate().any(|(fei, fe)| {
            edge_map[fei] == Some(cei)
                && !fe.support.is_empty()
                && chart_map[fe.left_idx] == ce.left_idx
                && chart_map[fe.right_idx] == ce.right_idx
        });
        if !has_lift {
            c2_edge_lift = false;
            break;
        }
    }

    // C3: 各非空粗 chart fiber 上の有理 1-cycle がすべて内部 block face の境界の有理線形結合で表せる。
    let c3_fiber_rational_1_cycles =
        check_c3_rational_1_cycles(&coarse_nerve, &fine_nerve, &chart_map)?;

    // C4: 各非空粗 face は、境界 3 辺が整合する非空細 face lift を少なくとも 1 つ持つ。
    let mut c4_face_lift = true;
    for (cfi, cf) in coarse_nerve.faces.iter().enumerate() {
        if cf.support.is_empty() {
            continue;
        }
        let has_lift = fine_nerve.faces.iter().enumerate().any(|(ffi, ff)| {
            face_map[ffi] == Some(cfi)
                && !ff.support.is_empty()
                && edge_map[ff.e0_idx] == Some(cf.e0_idx)
                && edge_map[ff.e1_idx] == Some(cf.e1_idx)
                && edge_map[ff.e2_idx] == Some(cf.e2_idx)
        });
        if !has_lift {
            c4_face_lift = false;
            break;
        }
    }

    // C5: 全体の nerve で各粗 edge の declared fine edge lift は高々 1 つ（Lean ConditionC5）。
    let mut seen_coarse_edges = BTreeSet::new();
    let mut c5_edge_lift_unique = true;
    for ce_opt in &edge_map {
        if let Some(cei) = ce_opt
            && !seen_coarse_edges.insert(*cei)
        {
            c5_edge_lift_unique = false;
            break;
        }
    }

    // C6: 粗 self-loop へ写る細 edge はすべて自身も self-loop である（Lean ConditionC6）。
    let mut c6_self_loop = true;
    for (fei, fe) in fine_nerve.edges.iter().enumerate() {
        if let Some(cei) = edge_map[fei] {
            let ce = &coarse_nerve.edges[cei];
            if ce.left_idx == ce.right_idx && fe.left_idx != fe.right_idx {
                c6_self_loop = false;
                break;
            }
        }
    }

    let all_passed = c0_support_image
        && c1_block_fiber_connected
        && c2_edge_lift
        && c3_fiber_rational_1_cycles
        && c4_face_lift
        && c5_edge_lift_unique
        && c6_self_loop;

    Ok(ConditionCResult {
        c0_support_image,
        c1_block_fiber_connected,
        c2_edge_lift,
        c3_fiber_rational_1_cycles,
        c4_face_lift,
        c5_edge_lift_unique,
        c6_self_loop,
        all_passed,
    })
}

fn check_c1_fiber_connected(
    coarse: &ComputedNerve,
    fine: &ComputedNerve,
    chart_map: &[usize],
) -> bool {
    for (ci, c_sup) in coarse.chart_supports.iter().enumerate() {
        if c_sup.is_empty() {
            continue;
        }
        let fiber_charts: Vec<usize> = fine
            .chart_supports
            .iter()
            .enumerate()
            .filter(|&(fi, f_sup)| chart_map[fi] == ci && !f_sup.is_empty())
            .map(|(fi, _)| fi)
            .collect();
        if fiber_charts.is_empty() {
            return false;
        }
        let f_pos: BTreeMap<usize, usize> = fiber_charts
            .iter()
            .enumerate()
            .map(|(idx, &fi)| (fi, idx))
            .collect();
        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); fiber_charts.len()];
        for fe in &fine.edges {
            if !fe.support.is_empty()
                && let (Some(&u), Some(&w)) = (f_pos.get(&fe.left_idx), f_pos.get(&fe.right_idx))
            {
                adj[u].push(w);
                adj[w].push(u);
            }
        }
        let mut visited = vec![false; fiber_charts.len()];
        let mut queue = VecDeque::new();
        visited[0] = true;
        queue.push_back(0);
        let mut seen = 0usize;
        while let Some(u) = queue.pop_front() {
            seen += 1;
            for &nxt in &adj[u] {
                if !visited[nxt] {
                    visited[nxt] = true;
                    queue.push_back(nxt);
                }
            }
        }
        if seen != fiber_charts.len() {
            return false;
        }
    }
    true
}

fn check_c3_rational_1_cycles(
    coarse: &ComputedNerve,
    fine: &ComputedNerve,
    chart_map: &[usize],
) -> Result<bool, SilenceReason> {
    for (ci, c_sup) in coarse.chart_supports.iter().enumerate() {
        if c_sup.is_empty() {
            continue;
        }
        let fiber_charts: Vec<usize> = fine
            .chart_supports
            .iter()
            .enumerate()
            .filter(|&(fi, f_sup)| chart_map[fi] == ci && !f_sup.is_empty())
            .map(|(fi, _)| fi)
            .collect();
        let f_chart_pos: BTreeMap<usize, usize> = fiber_charts
            .iter()
            .enumerate()
            .map(|(idx, &fi)| (fi, idx))
            .collect();
        let fiber_edges: Vec<usize> = fine
            .edges
            .iter()
            .enumerate()
            .filter(|(_, fe)| {
                !fe.support.is_empty()
                    && f_chart_pos.contains_key(&fe.left_idx)
                    && f_chart_pos.contains_key(&fe.right_idx)
            })
            .map(|(fei, _)| fei)
            .collect();
        if fiber_edges.is_empty() {
            continue;
        }
        let f_edge_pos: BTreeMap<usize, usize> = fiber_edges
            .iter()
            .enumerate()
            .map(|(idx, &fei)| (fei, idx))
            .collect();

        let mut del1 = vec![vec![Rat::zero(); fiber_edges.len()]; fiber_charts.len()];
        for (col, &fei) in fiber_edges.iter().enumerate() {
            let fe = &fine.edges[fei];
            let l = f_chart_pos[&fe.left_idx];
            let r = f_chart_pos[&fe.right_idx];
            del1[r][col] = del1[r][col].clone() + Rat::one();
            del1[l][col] = del1[l][col].clone() - Rat::one();
        }
        let zero_rhs = vec![Rat::zero(); fiber_charts.len()];
        let cycle_basis =
            match solve_affine_field(&del1, &zero_rhs, fiber_edges.len(), &Rat::zero())
                .map_err(map_atlas_alg_err)?
            {
                AffineSolutionField::Consistent { kernel_basis, .. } => kernel_basis,
                AffineSolutionField::Inconsistent { .. } => Vec::new(),
            };
        if cycle_basis.is_empty() {
            continue;
        }

        let internal_faces: Vec<usize> = fine
            .faces
            .iter()
            .enumerate()
            .filter(|(_, ff)| {
                !ff.support.is_empty()
                    && f_edge_pos.contains_key(&ff.e0_idx)
                    && f_edge_pos.contains_key(&ff.e1_idx)
                    && f_edge_pos.contains_key(&ff.e2_idx)
            })
            .map(|(ffi, _)| ffi)
            .collect();
        if internal_faces.is_empty() {
            return Ok(false);
        }

        let mut del2 = vec![vec![Rat::zero(); internal_faces.len()]; fiber_edges.len()];
        for (col, &ffi) in internal_faces.iter().enumerate() {
            let ff = &fine.faces[ffi];
            del2[f_edge_pos[&ff.e0_idx]][col] =
                del2[f_edge_pos[&ff.e0_idx]][col].clone() + Rat::one();
            del2[f_edge_pos[&ff.e1_idx]][col] =
                del2[f_edge_pos[&ff.e1_idx]][col].clone() - Rat::one();
            del2[f_edge_pos[&ff.e2_idx]][col] =
                del2[f_edge_pos[&ff.e2_idx]][col].clone() + Rat::one();
        }
        for cyc in &cycle_basis {
            match solve_affine_field(&del2, cyc, internal_faces.len(), &Rat::zero())
                .map_err(map_atlas_alg_err)?
            {
                AffineSolutionField::Consistent { .. } => {}
                AffineSolutionField::Inconsistent { .. } => return Ok(false),
            }
        }
    }
    Ok(true)
}
