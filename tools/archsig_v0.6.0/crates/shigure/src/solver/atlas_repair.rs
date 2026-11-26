//! 有限連結単純グラフ上の制約付き修復（頂点許容集合 `H_V`・辺許容集合 `H_E`、G-141 G5・H8・W3）。

use crate::algebra::cochain::mat_vec;
use crate::algebra::scalar::RingCoeff;
use crate::ir::result::{ReevalCheck, SilenceReason};
use crate::ir::result_phase4::ConstrainedRepairSummary;
use crate::solver::atlas::{
    AtlasRingBackend, EvaluatedGraph, SpanningTreeData, apply_spanning_tree_phi,
    reevaluate_adapter_commutativity, vec_to_named_map,
};

pub(crate) fn solve_vertex_repair<B: AtlasRingBackend>(
    backend: &B,
    graph: &EvaluatedGraph<B::Coeff>,
    base_lambdas: &[B::Coeff],
    allowed_vertices: &[String],
) -> Result<ConstrainedRepairSummary, SilenceReason> {
    let d0_lam = mat_vec(&graph.d0, base_lambdas, &graph.zero);
    let rhs: Vec<B::Coeff> = graph
        .offsets
        .iter()
        .zip(&d0_lam)
        .map(|(b, dl)| b.sub_ref(dl))
        .collect();
    let allowed_indices: Vec<usize> = allowed_vertices.iter().map(|v| graph.v_idx[v]).collect();
    let mat = restrict_columns(&graph.d0, &allowed_indices);
    match backend.solve_affine(&mat, &rhs, allowed_indices.len())? {
        (Some(particular), kernel_basis) => {
            let full_delta = expand_restricted(
                &particular,
                &allowed_indices,
                graph.vertices.len(),
                &graph.zero,
            );
            let repaired_lam: Vec<B::Coeff> = base_lambdas
                .iter()
                .zip(&full_delta)
                .map(|(l, a)| l.add_ref(a))
                .collect();
            let context = format!("vertex_constrained_repair{}", backend.reeval_suffix());
            let reeval = reevaluate_adapter_commutativity(
                graph,
                &repaired_lam,
                &graph.offsets,
                &context,
            );
            let basis_maps = kernel_basis
                .iter()
                .map(|v| {
                    vec_to_named_map(
                        &graph.vertices,
                        &expand_restricted(v, &allowed_indices, graph.vertices.len(), &graph.zero),
                    )
                })
                .collect();
            Ok(ConstrainedRepairSummary {
                allowed_items: allowed_vertices.to_vec(),
                repair_exists: true,
                particular_delta: Some(vec_to_named_map(&graph.vertices, &full_delta)),
                torsor_basis: basis_maps,
                h0_operation_torsor_rank: kernel_basis.len(),
                reevaluation: Some(reeval),
            })
        }
        (None, _) => Ok(ConstrainedRepairSummary {
            allowed_items: allowed_vertices.to_vec(),
            repair_exists: false,
            particular_delta: None,
            torsor_basis: Vec::new(),
            h0_operation_torsor_rank: 0,
            reevaluation: None,
        }),
    }
}

pub(crate) fn solve_edge_repair<B: AtlasRingBackend>(
    backend: &B,
    graph: &EvaluatedGraph<B::Coeff>,
    tree: &SpanningTreeData,
    allowed_edges: &[String],
) -> Result<ConstrainedRepairSummary, SilenceReason> {
    let allowed_indices: Vec<usize> = allowed_edges.iter().map(|e| graph.e_idx[e]).collect();
    let (mat, rhs) = build_edge_repair_system(graph, tree, &allowed_indices);
    let edge_names: Vec<String> = graph.edges.iter().map(|e| e.name.clone()).collect();
    match backend.solve_affine(&mat, &rhs, allowed_indices.len())? {
        (Some(particular), kernel_basis) => {
            let full_db = expand_restricted(
                &particular,
                &allowed_indices,
                graph.edges.len(),
                &graph.zero,
            );
            let repaired_b: Vec<B::Coeff> = graph
                .offsets
                .iter()
                .zip(&full_db)
                .map(|(b, db)| b.add_ref(db))
                .collect();
            let context = format!("edge_constrained_repair{}", backend.reeval_suffix());
            let (reeval, h0_rank) =
                match backend.solve_affine(&graph.d0, &repaired_b, graph.vertices.len())? {
                    (Some(lam_sol), lam_ker) => (
                        reevaluate_adapter_commutativity(graph, &lam_sol, &repaired_b, &context),
                        lam_ker.len(),
                    ),
                    (None, _) => (
                        ReevalCheck {
                            checked: true,
                            matched: false,
                            detail: backend.inconsistent_edge_repair_detail().to_owned(),
                        },
                        0,
                    ),
                };
            let basis_maps = kernel_basis
                .iter()
                .map(|v| {
                    vec_to_named_map(
                        &edge_names,
                        &expand_restricted(v, &allowed_indices, graph.edges.len(), &graph.zero),
                    )
                })
                .collect();
            Ok(ConstrainedRepairSummary {
                allowed_items: allowed_edges.to_vec(),
                repair_exists: true,
                particular_delta: Some(vec_to_named_map(&edge_names, &full_db)),
                torsor_basis: basis_maps,
                h0_operation_torsor_rank: h0_rank,
                reevaluation: Some(reeval),
            })
        }
        (None, _) => Ok(ConstrainedRepairSummary {
            allowed_items: allowed_edges.to_vec(),
            repair_exists: false,
            particular_delta: None,
            torsor_basis: Vec::new(),
            h0_operation_torsor_rank: 0,
            reevaluation: None,
        }),
    }
}

fn build_edge_repair_system<C: RingCoeff>(
    graph: &EvaluatedGraph<C>,
    tree: &SpanningTreeData,
    allowed_indices: &[usize],
) -> (Vec<Vec<C>>, Vec<C>) {
    let n_chords = tree.chord_edge_indices.len();
    let phi_b = apply_spanning_tree_phi(graph, tree, &graph.offsets);
    let rhs: Vec<C> = phi_b.iter().map(|v| graph.zero.sub_ref(v)).collect();
    let mut mat = vec![vec![graph.zero.zero_like(); allowed_indices.len()]; n_chords];
    let one = graph.zero.one_like();
    for (col, &ei) in allowed_indices.iter().enumerate() {
        let mut unit = vec![graph.zero.zero_like(); graph.edges.len()];
        unit[ei] = one.clone();
        let img = apply_spanning_tree_phi(graph, tree, &unit);
        for (row, val) in img.into_iter().enumerate() {
            mat[row][col] = val;
        }
    }
    (mat, rhs)
}

fn restrict_columns<C: Clone>(mat: &[Vec<C>], cols: &[usize]) -> Vec<Vec<C>> {
    mat.iter()
        .map(|row| cols.iter().map(|&c| row[c].clone()).collect())
        .collect()
}

fn expand_restricted<C: RingCoeff>(
    vals: &[C],
    indices: &[usize],
    total: usize,
    zero: &C,
) -> Vec<C> {
    let mut full = vec![zero.zero_like(); total];
    for (v, &idx) in vals.iter().zip(indices) {
        full[idx] = v.clone();
    }
    full
}
