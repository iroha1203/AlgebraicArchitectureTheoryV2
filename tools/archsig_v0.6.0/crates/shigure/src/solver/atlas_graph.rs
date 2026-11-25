//! 有限連結単純グラフ評価・spanning tree `Φ_R`・SAGA 符号比較 `T`・
//! 原始 relation 連結性・K1 診断 `H^1` 階数・2x2 adapter 独立再評価検算
//! （G-141 G1–G4 / G-142 E1–E6）。

use crate::algebra::cochain::{mat_mul, mat_vec};
use crate::algebra::linear::smith_normal_form_z;
use crate::algebra::poly::{AlgebraError, Poly};
use crate::algebra::poly_expr::ExprBindings;
use crate::algebra::scalar::RingCoeff;
use crate::ir::atlas::GraphEdgeSpec;
use crate::ir::diagnostics::{ChartSupportSpec, NerveEdgeSpec, SupportedNerveSpec};
use crate::ir::result::{ReevalCheck, SilenceReason};
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::solver::atlas::map_atlas_alg_err;
use crate::solver::diagnostics::{
    build_diagnostic_complex, compute_nerve, evaluate_complex_over_domain,
};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

/// 評価済みの有向単純グラフ構造（粗・細グラフ共用）。
#[derive(Clone, Debug)]
pub(crate) struct EvaluatedGraph<C: RingCoeff> {
    pub(crate) vertices: Vec<String>,
    pub(crate) v_idx: BTreeMap<String, usize>,
    pub(crate) edges: Vec<EvaluatedEdge>,
    pub(crate) e_idx: BTreeMap<String, usize>,
    /// `|E| x |V|` グラフ微分 `(d^0 x)_e = x_{to(e)} - x_{from(e)}`。
    pub(crate) d0: Vec<Vec<C>>,
    pub(crate) offsets: Vec<C>,
    pub(crate) zero: C,
}

#[derive(Clone, Debug)]
pub(crate) struct EvaluatedEdge {
    pub(crate) name: String,
    pub(crate) from: usize,
    pub(crate) to: usize,
}

/// Spanning tree 分解（E5）。
#[derive(Clone, Debug)]
pub(crate) struct SpanningTreeData {
    /// 根頂点から各頂点への `(parent_vertex, child_vertex, edge_idx, edge_points_parent_to_child)`。
    pub(crate) bfs_order: Vec<(usize, usize, usize, bool)>,
    pub(crate) tree_edge_indices: Vec<usize>,
    pub(crate) chord_edge_indices: Vec<usize>,
}

pub(crate) fn is_graph_connected(vertices: &[String], edges: &[GraphEdgeSpec]) -> bool {
    if vertices.is_empty() {
        return false;
    }
    let v_idx: BTreeMap<&str, usize> = vertices
        .iter()
        .enumerate()
        .map(|(i, v)| (v.as_str(), i))
        .collect();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); vertices.len()];
    for e in edges {
        if let (Some(&u), Some(&w)) = (v_idx.get(e.from.as_str()), v_idx.get(e.to.as_str())) {
            adj[u].push(w);
            adj[w].push(u);
        }
    }
    let mut visited = vec![false; vertices.len()];
    let mut queue = VecDeque::new();
    visited[0] = true;
    queue.push_back(0);
    let mut count = 0usize;
    while let Some(u) = queue.pop_front() {
        count += 1;
        for &next in &adj[u] {
            if !visited[next] {
                visited[next] = true;
                queue.push_back(next);
            }
        }
    }
    count == vertices.len()
}

pub(crate) fn eval_const_expr<C, FE>(
    expr: &PolyExpr,
    empty_bindings: &ExprBindings,
    expand: &FE,
) -> Result<C, SilenceReason>
where
    C: RingCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
{
    let poly = expand(expr, empty_bindings).map_err(map_atlas_alg_err)?;
    poly.eval_at(&[]).map_err(map_atlas_alg_err)
}

pub(crate) fn build_evaluated_graph<C, FE>(
    vertices: &[String],
    edges: &[GraphEdgeSpec],
    zero: C,
    empty_bindings: &ExprBindings,
    expand: &FE,
) -> Result<EvaluatedGraph<C>, SilenceReason>
where
    C: RingCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
{
    let mut v_idx = BTreeMap::new();
    for (i, v) in vertices.iter().enumerate() {
        v_idx.insert(v.clone(), i);
    }
    let one = zero.one_like();
    let neg_one = zero.sub_ref(&one);
    let mut eval_edges = Vec::with_capacity(edges.len());
    let mut e_idx = BTreeMap::new();
    let mut d0 = vec![vec![zero.clone(); vertices.len()]; edges.len()];
    let mut offsets = Vec::with_capacity(edges.len());

    for (i, e) in edges.iter().enumerate() {
        let from = v_idx[&e.from];
        let to = v_idx[&e.to];
        let offset = eval_const_expr(&e.offset, empty_bindings, expand)?;
        d0[i][to] = one.clone();
        d0[i][from] = neg_one.clone();
        e_idx.insert(e.name.clone(), i);
        offsets.push(offset);
        eval_edges.push(EvaluatedEdge {
            name: e.name.clone(),
            from,
            to,
        });
    }

    Ok(EvaluatedGraph {
        vertices: vertices.to_vec(),
        v_idx,
        edges: eval_edges,
        e_idx,
        d0,
        offsets,
        zero,
    })
}

/// 決定論的 BFS で根頂点 0 からの spanning tree と chord を構成する（G-142 E5）。
pub(crate) fn build_spanning_tree<C: RingCoeff>(graph: &EvaluatedGraph<C>) -> SpanningTreeData {
    let n = graph.vertices.len();
    let mut adj: Vec<Vec<(usize, usize, bool)>> = vec![Vec::new(); n];
    for (ei, e) in graph.edges.iter().enumerate() {
        adj[e.from].push((e.to, ei, true));
        adj[e.to].push((e.from, ei, false));
    }
    let mut visited = vec![false; n];
    let mut queue = VecDeque::new();
    let mut bfs_order = Vec::new();
    let mut tree_edge_set = BTreeSet::new();
    visited[0] = true;
    queue.push_back(0);
    while let Some(u) = queue.pop_front() {
        for &(next, ei, forward) in &adj[u] {
            if !visited[next] {
                visited[next] = true;
                tree_edge_set.insert(ei);
                bfs_order.push((u, next, ei, forward));
                queue.push_back(next);
            }
        }
    }
    let tree_edge_indices: Vec<usize> = (0..graph.edges.len())
        .filter(|ei| tree_edge_set.contains(ei))
        .collect();
    let chord_edge_indices: Vec<usize> = (0..graph.edges.len())
        .filter(|ei| !tree_edge_set.contains(ei))
        .collect();
    SpanningTreeData {
        bfs_order,
        tree_edge_indices,
        chord_edge_indices,
    }
}

/// E5 の spanning tree 同型 `Φ_R(a) = (a_e - (d^0 u(a))_e)_{e ∉ T_Γ} ∈ R^{|E| - |V| + 1}`。
pub(crate) fn apply_spanning_tree_phi<C: RingCoeff>(
    graph: &EvaluatedGraph<C>,
    tree: &SpanningTreeData,
    a: &[C],
) -> Vec<C> {
    let mut u = vec![graph.zero.zero_like(); graph.vertices.len()];
    for &(parent, child, ei, forward) in &tree.bfs_order {
        u[child] = if forward {
            u[parent].add_ref(&a[ei])
        } else {
            u[parent].sub_ref(&a[ei])
        };
    }
    let d0u = mat_vec(&graph.d0, &u, &graph.zero);
    tree.chord_edge_indices
        .iter()
        .map(|&ei| a[ei].sub_ref(&d0u[ei]))
        .collect()
}

/// G4: SAGA 増加 pair 微分 `δ^0_SAGA` と符号比較写像 `T` の可換性 `T * δ^0_SAGA == d^0_Γ` を検算する。
pub(crate) fn verify_saga_sign_comparison<C: RingCoeff>(graph: &EvaluatedGraph<C>) -> bool {
    let m = graph.edges.len();
    let n = graph.vertices.len();
    let one = graph.zero.one_like();
    let neg_one = graph.zero.sub_ref(&one);
    let mut delta_saga = vec![vec![graph.zero.zero_like(); n]; m];
    let mut t_mat = vec![vec![graph.zero.zero_like(); m]; m];
    for (ei, e) in graph.edges.iter().enumerate() {
        let (lo, hi) = if e.from < e.to {
            (e.from, e.to)
        } else {
            (e.to, e.from)
        };
        delta_saga[ei][hi] = one.clone();
        delta_saga[ei][lo] = neg_one.clone();
        t_mat[ei][ei] = if e.from < e.to {
            one.clone()
        } else {
            neg_one.clone()
        };
    }
    let prod = mat_mul(&t_mat, &delta_saga, n, &graph.zero);
    prod == graph.d0
}

/// E2: 原始補正 relation 群 `M = Z^E / <[e] - [e'] : e, e' が頂点を共有>` が `Z` と同型かを SNF で検算する。
pub(crate) fn verify_primitive_relation_connected<C: RingCoeff>(
    graph: &EvaluatedGraph<C>,
) -> Result<bool, SilenceReason> {
    let m = graph.edges.len();
    let mut incident: Vec<Vec<usize>> = vec![Vec::new(); graph.vertices.len()];
    for (ei, e) in graph.edges.iter().enumerate() {
        incident[e.from].push(ei);
        incident[e.to].push(ei);
    }
    let mut rel_rows: Vec<Vec<BigInt>> = Vec::new();
    for inc in &incident {
        if inc.len() >= 2 {
            let e0 = inc[0];
            for &ek in &inc[1..] {
                let mut row = vec![BigInt::zero(); m];
                row[ek] = BigInt::one();
                row[e0] = -BigInt::one();
                rel_rows.push(row);
            }
        }
    }
    let snf = smith_normal_form_z(&rel_rows, m).map_err(map_atlas_alg_err)?;
    let free_rank = m - snf.rank;
    let torsion_free = snf.diagonals.iter().all(|d| *d == BigInt::one());
    Ok(free_rank == 1 && torsion_free)
}

/// E1/E3/E6: 補正 readout `p(v) = 1 - 1 = 0` から K1 診断複体 `C_R` を生成し、
/// `diagnostic_h1_rank`（offset 独立な一定階数 `|E| - |V| + 1`）を独立計算する。
pub(crate) fn compute_graph_diagnostic_h1_rank<C: RingCoeff>(
    graph: &EvaluatedGraph<C>,
    coeff_domain: &CoeffDomain,
) -> Result<usize, SilenceReason> {
    let mut charts = Vec::with_capacity(graph.vertices.len());
    for (vi, vname) in graph.vertices.iter().enumerate() {
        let sup: Vec<String> = graph
            .edges
            .iter()
            .filter(|e| e.from == vi || e.to == vi)
            .map(|e| e.name.clone())
            .collect();
        charts.push(ChartSupportSpec {
            name: vname.clone(),
            support: sup,
        });
    }
    let edges: Vec<NerveEdgeSpec> = graph
        .edges
        .iter()
        .map(|e| NerveEdgeSpec {
            name: e.name.clone(),
            left: graph.vertices[e.from].clone(),
            right: graph.vertices[e.to].clone(),
        })
        .collect();
    let nerve = compute_nerve(&SupportedNerveSpec {
        charts,
        edges,
        faces: Vec::new(),
    })?;
    let one = graph.zero.one_like();
    let neg_one = graph.zero.sub_ref(&one);
    let pv = one.add_ref(&neg_one);
    let pv_str = pv.to_string();
    let mut law_vals = BTreeMap::new();
    let mut inner = BTreeMap::new();
    for e in &graph.edges {
        inner.insert(e.name.clone(), pv_str.clone());
    }
    law_vals.insert("p_of_v".to_owned(), inner);
    let cpx = build_diagnostic_complex(&nerve, &law_vals);
    let sum = evaluate_complex_over_domain(&cpx, coeff_domain)?;
    Ok(sum.h1_free_rank)
}

/// 原始 2x2 台帳 adapter `g_b = I + b v p`、`i_λ = (λ, 1-λ)^T`、`p = (1, 1)` による独立再評価検算（G1）。
pub(crate) fn reevaluate_adapter_commutativity<C: RingCoeff>(
    graph: &EvaluatedGraph<C>,
    lambdas: &[C],
    offsets: &[C],
    context: &str,
) -> ReevalCheck {
    let one = graph.zero.one_like();
    let mut mismatches = Vec::new();
    for (vi, lam) in lambdas.iter().enumerate() {
        let c0 = lam.clone();
        let c1 = one.sub_ref(lam);
        let read = c0.add_ref(&c1);
        if read != one {
            mismatches.push(format!("p(i_{})={read} != 1", graph.vertices[vi]));
        }
    }
    for (ei, e) in graph.edges.iter().enumerate() {
        let b = &offsets[ei];
        let li = &lambdas[e.from];
        let lj = &lambdas[e.to];
        let li_0 = li.clone();
        let li_1 = one.sub_ref(li);
        let lj_0 = lj.clone();
        let lj_1 = one.sub_ref(lj);

        let g00 = one.add_ref(b);
        let g01 = b.clone();
        let g10 = graph.zero.sub_ref(b);
        let g11 = one.sub_ref(b);

        let lhs0 = g00.mul_ref(&li_0).add_ref(&g01.mul_ref(&li_1));
        let lhs1 = g10.mul_ref(&li_0).add_ref(&g11.mul_ref(&li_1));
        if lhs0 != lj_0 || lhs1 != lj_1 {
            mismatches.push(format!(
                "edge `{}`: g_b(i_from)=({lhs0}, {lhs1}) != i_to=({lj_0}, {lj_1})",
                e.name
            ));
        }
    }
    ReevalCheck {
        checked: true,
        matched: mismatches.is_empty(),
        detail: if mismatches.is_empty() {
            format!(
                "{context}: g_{{b_e}} i_{{lambda_from}} = i_{{lambda_to}} and p(i_lambda) = 1 verified on all {} edges",
                graph.edges.len()
            )
        } else {
            format!("{context}: mismatches: {}", mismatches.join("; "))
        },
    }
}
