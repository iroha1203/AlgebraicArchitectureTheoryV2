//! 有限連結単純グラフ上の制約付き修復（頂点許容集合 `H_V`・辺許容集合 `H_E`、G-141 G5・H8・W3）。

use crate::algebra::artin::{AffineSolutionField, solve_affine_field};
use crate::algebra::cochain::mat_vec;
use crate::algebra::linear::{AffineSolutionZ, solve_affine_z};
use crate::algebra::scalar::RingCoeff;
use crate::algebra::syzygy::FieldCoeff;
use crate::ir::result::{ReevalCheck, SilenceReason};
use crate::ir::result_phase4::ConstrainedRepairSummary;
use crate::solver::atlas::{
    EvaluatedGraph, SpanningTreeData, apply_spanning_tree_phi, map_atlas_alg_err,
    reevaluate_adapter_commutativity, vec_to_named_map,
};
use num_bigint::BigInt;
use num_traits::Zero;

pub(crate) fn solve_vertex_repair_field<C: FieldCoeff>(
    graph: &EvaluatedGraph<C>,
    base_lambdas: &[C],
    allowed_vertices: &[String],
) -> Result<ConstrainedRepairSummary, SilenceReason> {
    let d0_lam = mat_vec(&graph.d0, base_lambdas, &graph.zero);
    let rhs: Vec<C> = graph
        .offsets
        .iter()
        .zip(&d0_lam)
        .map(|(b, dl)| b.sub_ref(dl))
        .collect();
    let allowed_indices: Vec<usize> = allowed_vertices.iter().map(|v| graph.v_idx[v]).collect();
    let mat = restrict_columns(&graph.d0, &allowed_indices);
    match solve_affine_field(&mat, &rhs, allowed_indices.len(), &graph.zero)
        .map_err(map_atlas_alg_err)?
    {
        AffineSolutionField::Consistent {
            particular,
            kernel_basis,
            ..
        } => {
            let full_delta = expand_restricted(
                &particular,
                &allowed_indices,
                graph.vertices.len(),
                &graph.zero,
            );
            let repaired_lam: Vec<C> = base_lambdas
                .iter()
                .zip(&full_delta)
                .map(|(l, a)| l.add_ref(a))
                .collect();
            let reeval = reevaluate_adapter_commutativity(
                graph,
                &repaired_lam,
                &graph.offsets,
                "vertex_constrained_repair",
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
        AffineSolutionField::Inconsistent { .. } => Ok(ConstrainedRepairSummary {
            allowed_items: allowed_vertices.to_vec(),
            repair_exists: false,
            particular_delta: None,
            torsor_basis: Vec::new(),
            h0_operation_torsor_rank: 0,
            reevaluation: None,
        }),
    }
}

pub(crate) fn solve_vertex_repair_z(
    graph: &EvaluatedGraph<BigInt>,
    base_lambdas: &[BigInt],
    allowed_vertices: &[String],
) -> Result<ConstrainedRepairSummary, SilenceReason> {
    let d0_lam = mat_vec(&graph.d0, base_lambdas, &BigInt::zero());
    let rhs: Vec<BigInt> = graph
        .offsets
        .iter()
        .zip(&d0_lam)
        .map(|(b, dl)| b - dl)
        .collect();
    let allowed_indices: Vec<usize> = allowed_vertices.iter().map(|v| graph.v_idx[v]).collect();
    let mat = restrict_columns(&graph.d0, &allowed_indices);
    match solve_affine_z(&mat, &rhs, allowed_indices.len()).map_err(map_atlas_alg_err)? {
        AffineSolutionZ::Consistent {
            particular,
            kernel_basis,
            ..
        } => {
            let full_delta = expand_restricted(
                &particular,
                &allowed_indices,
                graph.vertices.len(),
                &BigInt::zero(),
            );
            let repaired_lam: Vec<BigInt> = base_lambdas
                .iter()
                .zip(&full_delta)
                .map(|(l, a)| l + a)
                .collect();
            let reeval = reevaluate_adapter_commutativity(
                graph,
                &repaired_lam,
                &graph.offsets,
                "vertex_constrained_repair_z",
            );
            let basis_maps = kernel_basis
                .iter()
                .map(|v| {
                    vec_to_named_map(
                        &graph.vertices,
                        &expand_restricted(
                            v,
                            &allowed_indices,
                            graph.vertices.len(),
                            &BigInt::zero(),
                        ),
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
        AffineSolutionZ::Inconsistent { .. } => Ok(ConstrainedRepairSummary {
            allowed_items: allowed_vertices.to_vec(),
            repair_exists: false,
            particular_delta: None,
            torsor_basis: Vec::new(),
            h0_operation_torsor_rank: 0,
            reevaluation: None,
        }),
    }
}

pub(crate) fn solve_edge_repair_field<C: FieldCoeff>(
    graph: &EvaluatedGraph<C>,
    tree: &SpanningTreeData,
    allowed_edges: &[String],
) -> Result<ConstrainedRepairSummary, SilenceReason> {
    let allowed_indices: Vec<usize> = allowed_edges.iter().map(|e| graph.e_idx[e]).collect();
    let (mat, rhs) = build_edge_repair_system(graph, tree, &allowed_indices);
    let edge_names: Vec<String> = graph.edges.iter().map(|e| e.name.clone()).collect();
    match solve_affine_field(&mat, &rhs, allowed_indices.len(), &graph.zero)
        .map_err(map_atlas_alg_err)?
    {
        AffineSolutionField::Consistent {
            particular,
            kernel_basis,
            ..
        } => {
            let full_db = expand_restricted(
                &particular,
                &allowed_indices,
                graph.edges.len(),
                &graph.zero,
            );
            let repaired_b: Vec<C> = graph
                .offsets
                .iter()
                .zip(&full_db)
                .map(|(b, db)| b.add_ref(db))
                .collect();
            let reeval = match solve_affine_field(
                &graph.d0,
                &repaired_b,
                graph.vertices.len(),
                &graph.zero,
            )
            .map_err(map_atlas_alg_err)?
            {
                AffineSolutionField::Consistent {
                    particular: lam_sol,
                    ..
                } => reevaluate_adapter_commutativity(
                    graph,
                    &lam_sol,
                    &repaired_b,
                    "edge_constrained_repair",
                ),
                AffineSolutionField::Inconsistent { .. } => ReevalCheck {
                    checked: true,
                    matched: false,
                    detail: "repaired offset b + delta_b did not admit a global operation"
                        .to_owned(),
                },
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
                h0_operation_torsor_rank: 1,
                reevaluation: Some(reeval),
            })
        }
        AffineSolutionField::Inconsistent { .. } => Ok(ConstrainedRepairSummary {
            allowed_items: allowed_edges.to_vec(),
            repair_exists: false,
            particular_delta: None,
            torsor_basis: Vec::new(),
            h0_operation_torsor_rank: 0,
            reevaluation: None,
        }),
    }
}

pub(crate) fn solve_edge_repair_z(
    graph: &EvaluatedGraph<BigInt>,
    tree: &SpanningTreeData,
    allowed_edges: &[String],
) -> Result<ConstrainedRepairSummary, SilenceReason> {
    let allowed_indices: Vec<usize> = allowed_edges.iter().map(|e| graph.e_idx[e]).collect();
    let (mat, rhs) = build_edge_repair_system(graph, tree, &allowed_indices);
    let edge_names: Vec<String> = graph.edges.iter().map(|e| e.name.clone()).collect();
    match solve_affine_z(&mat, &rhs, allowed_indices.len()).map_err(map_atlas_alg_err)? {
        AffineSolutionZ::Consistent {
            particular,
            kernel_basis,
            ..
        } => {
            let full_db = expand_restricted(
                &particular,
                &allowed_indices,
                graph.edges.len(),
                &BigInt::zero(),
            );
            let repaired_b: Vec<BigInt> = graph
                .offsets
                .iter()
                .zip(&full_db)
                .map(|(b, db)| b + db)
                .collect();
            let reeval = match solve_affine_z(&graph.d0, &repaired_b, graph.vertices.len())
                .map_err(map_atlas_alg_err)?
            {
                AffineSolutionZ::Consistent {
                    particular: lam_sol,
                    ..
                } => reevaluate_adapter_commutativity(
                    graph,
                    &lam_sol,
                    &repaired_b,
                    "edge_constrained_repair_z",
                ),
                AffineSolutionZ::Inconsistent { .. } => ReevalCheck {
                    checked: true,
                    matched: false,
                    detail: "repaired offset b + delta_b did not admit an integer global operation"
                        .to_owned(),
                },
            };
            let basis_maps = kernel_basis
                .iter()
                .map(|v| {
                    vec_to_named_map(
                        &edge_names,
                        &expand_restricted(v, &allowed_indices, graph.edges.len(), &BigInt::zero()),
                    )
                })
                .collect();
            Ok(ConstrainedRepairSummary {
                allowed_items: allowed_edges.to_vec(),
                repair_exists: true,
                particular_delta: Some(vec_to_named_map(&edge_names, &full_db)),
                torsor_basis: basis_maps,
                h0_operation_torsor_rank: 1,
                reevaluation: Some(reeval),
            })
        }
        AffineSolutionZ::Inconsistent { .. } => Ok(ConstrainedRepairSummary {
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
