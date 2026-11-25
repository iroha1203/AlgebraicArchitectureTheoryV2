//! 有限連結単純グラフ上の実 adapter・SAGA 符号比較・spanning tree $\Phi_R$・
//! 指定診断類 $\kappa_b$・制約付き全修復（$H_V, H_E$）・Atlas 細分化・拡張言語非移送の計算核
//! （G-141 G1–G5・H8・H12 / G-142 E1–E6・F1–F7・W3 / AC6・AC7）。

use crate::algebra::artin::{AffineSolutionField, solve_affine_field};
use crate::algebra::cochain::mat_vec;
use crate::algebra::linear::{AffineSolutionZ, solve_affine_z};
use crate::algebra::poly::{AlgebraError, Poly};
use crate::algebra::poly_expr::ExprBindings;
use crate::algebra::scalar::{FpElem, Rat, RingCoeff};
use crate::algebra::syzygy::FieldCoeff;
use crate::ir::atlas::{AtlasTaskSpec, CheckedAtlasTask};
use crate::ir::change::PointDomain;
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{ApplicabilityCheck, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_phase4::AtlasOutcomeDetail;
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::solver::atlas_ext::compute_extended_language_check;
pub(crate) use crate::solver::atlas_graph::{
    EvaluatedEdge, EvaluatedGraph, SpanningTreeData, apply_spanning_tree_phi,
    build_evaluated_graph, build_spanning_tree, compute_graph_diagnostic_h1_rank, eval_const_expr,
    is_graph_connected, reevaluate_adapter_commutativity, verify_primitive_relation_connected,
    verify_saga_sign_comparison,
};
use crate::solver::atlas_refinement::compute_atlas_refinement;
use crate::solver::atlas_repair::{
    solve_edge_repair_field, solve_edge_repair_z, solve_vertex_repair_field, solve_vertex_repair_z,
};
use num_bigint::BigInt;
use num_traits::Zero;
use std::collections::BTreeMap;

/// `CheckedAtlasTask` を実行し、実 adapter・SAGA 比較・制約付き修復・細分化・拡張言語検査を返す。
pub fn solve_atlas_task(task: &CheckedAtlasTask) -> ShigureOutcome {
    let spec = task.spec();
    let coeff_domain = spec.coeff_domain.clone();
    let point_domain = PointDomain::UniversalRing;
    let mut provenance = spec.provenance.clone();
    for clause in [
        MathClause::G141G1,
        MathClause::G141G4,
        MathClause::G141G5,
        MathClause::G142E1,
        MathClause::G142E2,
        MathClause::G142E5,
        MathClause::G142E6,
    ] {
        if !provenance.clauses.contains(&clause) {
            provenance.clauses.push(clause);
        }
    }
    let mut checks = Vec::new();

    if let CoeffDomain::Fp(p) = &coeff_domain
        && !archsig_common::prime::is_prime(p)
    {
        let detail = format!("modulus {p} is not prime");
        checks.push(ApplicabilityCheck::failed(
            "coeff_ring_valid",
            MathClause::G141G1,
            detail.clone(),
        ));
        return atlas_undetermined(
            coeff_domain.clone(),
            point_domain,
            checks,
            provenance,
            SilenceReason::UnsupportedCoeffRing {
                domain: coeff_domain,
                detail,
            },
        );
    }
    checks.push(ApplicabilityCheck::passed(
        "coeff_ring_valid",
        MathClause::G141G1,
    ));

    if !is_graph_connected(&spec.vertices, &spec.edges) {
        checks.push(ApplicabilityCheck::failed(
            "graph_connected",
            MathClause::G141G1,
            "graph is disconnected; G-141 G1 / G-142 E1 requires a finite connected simple graph",
        ));
        return atlas_undetermined(
            coeff_domain,
            point_domain,
            checks,
            provenance,
            SilenceReason::DisconnectedGraphOutOfScope {
                detail: format!(
                    "graph in atlas task `{}` is disconnected (|V|={}, |E|={})",
                    spec.name,
                    spec.vertices.len(),
                    spec.edges.len()
                ),
            },
        );
    }
    checks.push(ApplicabilityCheck::passed(
        "graph_connected",
        MathClause::G141G1,
    ));

    match &coeff_domain {
        CoeffDomain::Q => solve_atlas_field(
            spec,
            Rat::zero(),
            "Q".to_owned(),
            &|e, b| Poly::from_expr_q(e, b),
            checks,
            provenance,
        ),
        CoeffDomain::Fp(p) => {
            let zero_fp = FpElem::from_checked_prime(BigInt::zero(), p.clone());
            let p1 = p.clone();
            solve_atlas_field(
                spec,
                zero_fp,
                format!("F_{p}"),
                &move |e, b| Poly::from_expr_fp(e, b, &p1),
                checks,
                provenance,
            )
        }
        CoeffDomain::Z => solve_atlas_z(spec, checks, provenance),
    }
}

fn solve_atlas_field<C, FE>(
    spec: &AtlasTaskSpec,
    zero: C,
    coeff_label: String,
    expand: &FE,
    mut checks: Vec<ApplicabilityCheck>,
    mut provenance: Provenance,
) -> ShigureOutcome
where
    C: FieldCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
{
    let coeff_domain = spec.coeff_domain.clone();
    let point_domain = PointDomain::UniversalRing;
    let (_, empty_bindings) = match ExprBindings::from_slices(&[], &[], &[]) {
        Ok(b) => b,
        Err(e) => {
            return atlas_undetermined(
                coeff_domain,
                point_domain,
                checks,
                provenance,
                map_atlas_alg_err(e),
            );
        }
    };

    // mu の評価（Unobserved 検出を含む）。
    if let Err(reason) = eval_const_expr(&spec.mu, &empty_bindings, expand) {
        return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
    }

    let graph = match build_evaluated_graph(&spec.vertices, &spec.edges, zero.clone(), &empty_bindings, expand) {
        Ok(g) => g,
        Err(reason) => {
            return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };

    let base_lambdas = match eval_vertex_map(&spec.vertices, &spec.base_lambdas, &empty_bindings, expand) {
        Ok(v) => v,
        Err(reason) => {
            return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };

    let saga_ok = verify_saga_sign_comparison(&graph);
    checks.push(ApplicabilityCheck {
        condition: "saga_sign_comparison_commutes".to_owned(),
        clause: MathClause::G141G4,
        satisfied: saga_ok,
        detail: None,
    });

    let prim_rel_ok = match verify_primitive_relation_connected(&graph) {
        Ok(ok) => ok,
        Err(reason) => {
            return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };
    let diagnostic_h1_rank = match compute_graph_diagnostic_h1_rank(&graph, &coeff_domain) {
        Ok(r) => r,
        Err(reason) => {
            return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };

    // 実残差 r = d^0 λ - b と spanning tree 座標 Φ_R(r) = Φ_R(-b)。
    let d0_lam = mat_vec(&graph.d0, &base_lambdas, &zero);
    let residuals: Vec<C> = d0_lam
        .iter()
        .zip(&graph.offsets)
        .map(|(d, b)| d.sub_ref(b))
        .collect();
    let real_residuals: BTreeMap<String, String> = graph
        .edges
        .iter()
        .zip(&residuals)
        .map(|(e, r)| (e.name.clone(), r.to_string()))
        .collect();

    let tree = build_spanning_tree(&graph);
    let phi_r = apply_spanning_tree_phi(&graph, &tree, &residuals);
    let o_b_coords: Vec<String> = phi_r.iter().map(ToString::to_string).collect();
    let o_b_is_zero = phi_r.iter().all(RingCoeff::coeff_is_zero);

    // 無制約全大域操作 d^0 λ' = b。
    let (unc_exists, unc_particular, unc_h0_rank, unc_reeval) =
        match solve_affine_field(&graph.d0, &graph.offsets, graph.vertices.len(), &zero) {
            Ok(AffineSolutionField::Consistent {
                particular,
                kernel_basis,
                ..
            }) => {
                let reeval = reevaluate_adapter_commutativity(
                    &graph,
                    &particular,
                    &graph.offsets,
                    "unconstrained_global_operation",
                );
                let map = vec_to_named_map(&graph.vertices, &particular);
                (true, Some(map), kernel_basis.len(), Some(reeval))
            }
            Ok(AffineSolutionField::Inconsistent { .. }) => (false, None, 0, None),
            Err(e) => {
                return atlas_undetermined(
                    coeff_domain,
                    point_domain,
                    checks,
                    provenance,
                    map_atlas_alg_err(e),
                );
            }
        };

    // 頂点許容修復 H_V: d^0|_{H_V} a = b - d^0 λ。
    let vertex_constrained_repair = match solve_vertex_repair_field(
        &graph,
        &base_lambdas,
        &spec.allowed_vertices,
    ) {
        Ok(s) => s,
        Err(reason) => {
            return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };

    // 辺許容修復 H_E: Φ_R(Δb|_{H_E}) = -Φ_R(b)。
    let edge_constrained_repair =
        match solve_edge_repair_field(&graph, &tree, &spec.allowed_edges) {
            Ok(s) => s,
            Err(reason) => {
                return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        };

    // Atlas 細分化（F1–F7）。
    let refinement = if let Some(ref_spec) = &spec.refinement {
        for clause in [
            MathClause::G142F1,
            MathClause::G142F2,
            MathClause::G142F3,
            MathClause::G142F4,
            MathClause::G142F5,
        ] {
            if !provenance.clauses.contains(&clause) {
                provenance.clauses.push(clause);
            }
        }
        match compute_atlas_refinement(
            spec,
            ref_spec,
            &graph,
            &base_lambdas,
            &tree,
            &phi_r,
            &empty_bindings,
            expand,
            &|mat, rhs, n_vars| match solve_affine_field(mat, rhs, n_vars, &zero)
                .map_err(map_atlas_alg_err)?
            {
                AffineSolutionField::Consistent {
                    particular,
                    kernel_basis,
                    ..
                } => Ok((Some(particular), kernel_basis)),
                AffineSolutionField::Inconsistent { .. } => Ok((None, Vec::new())),
            },
        ) {
            Ok(r) => Some(r),
            Err(reason) => {
                return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        }
    } else {
        None
    };

    // 拡張言語非移送検査（H12）。
    let extended_language_non_transport = if let Some(ext) = &spec.extended_language_check {
        if !provenance.clauses.contains(&MathClause::G141H12) {
            provenance.clauses.push(MathClause::G141H12);
        }
        match compute_extended_language_check(ext, zero.clone(), expand) {
            Ok(r) => Some(r),
            Err(reason) => {
                return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        }
    } else {
        None
    };

    let verdict = determine_atlas_verdict(
        o_b_is_zero,
        refinement.as_ref(),
        extended_language_non_transport.as_ref(),
    );

    let detail = AtlasOutcomeDetail {
        coeff_ring_label: coeff_label,
        num_vertices: graph.vertices.len(),
        num_edges: graph.edges.len(),
        graph_connected: true,
        saga_sign_commutes_verified: saga_ok,
        real_residuals,
        spanning_tree_edges: tree
            .tree_edge_indices
            .iter()
            .map(|&i| graph.edges[i].name.clone())
            .collect(),
        chord_edges: tree
            .chord_edge_indices
            .iter()
            .map(|&i| graph.edges[i].name.clone())
            .collect(),
        designated_class_o_b_coords: o_b_coords.clone(),
        designated_class_kappa_b_coords: o_b_coords,
        o_b_is_zero,
        kappa_b_is_zero: o_b_is_zero,
        diagnostic_h1_rank,
        primitive_relation_connected_verified: prim_rel_ok,
        z_to_q_zero_reflection_verified: None,
        unconstrained_global_operation_exists: unc_exists,
        unconstrained_particular_lambda: unc_particular,
        unconstrained_h0_torsor_rank: unc_h0_rank,
        unconstrained_reevaluation: unc_reeval,
        vertex_constrained_repair,
        edge_constrained_repair,
        refinement,
        extended_language_non_transport,
    };

    atlas_outcome(verdict, coeff_domain, point_domain, checks, provenance, detail)
}

fn solve_atlas_z(
    spec: &AtlasTaskSpec,
    mut checks: Vec<ApplicabilityCheck>,
    mut provenance: Provenance,
) -> ShigureOutcome {
    let coeff_domain = CoeffDomain::Z;
    let point_domain = PointDomain::UniversalRing;
    let (_, empty_bindings) = match ExprBindings::from_slices(&[], &[], &[]) {
        Ok(b) => b,
        Err(e) => {
            return atlas_undetermined(
                coeff_domain,
                point_domain,
                checks,
                provenance,
                map_atlas_alg_err(e),
            );
        }
    };
    let expand = |e: &PolyExpr, b: &ExprBindings| Poly::from_expr_z(e, b);

    if let Err(reason) = eval_const_expr(&spec.mu, &empty_bindings, &expand) {
        return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
    }
    let graph = match build_evaluated_graph(
        &spec.vertices,
        &spec.edges,
        BigInt::zero(),
        &empty_bindings,
        &expand,
    ) {
        Ok(g) => g,
        Err(reason) => {
            return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };
    let base_lambdas = match eval_vertex_map(&spec.vertices, &spec.base_lambdas, &empty_bindings, &expand) {
        Ok(v) => v,
        Err(reason) => {
            return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };

    let saga_ok = verify_saga_sign_comparison(&graph);
    checks.push(ApplicabilityCheck {
        condition: "saga_sign_comparison_commutes".to_owned(),
        clause: MathClause::G141G4,
        satisfied: saga_ok,
        detail: None,
    });
    let prim_rel_ok = match verify_primitive_relation_connected(&graph) {
        Ok(ok) => ok,
        Err(reason) => {
            return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };
    let diagnostic_h1_rank = match compute_graph_diagnostic_h1_rank(&graph, &coeff_domain) {
        Ok(r) => r,
        Err(reason) => {
            return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };

    let d0_lam = mat_vec(&graph.d0, &base_lambdas, &BigInt::zero());
    let residuals: Vec<BigInt> = d0_lam
        .iter()
        .zip(&graph.offsets)
        .map(|(d, b)| d - b)
        .collect();
    let real_residuals: BTreeMap<String, String> = graph
        .edges
        .iter()
        .zip(&residuals)
        .map(|(e, r)| (e.name.clone(), r.to_string()))
        .collect();

    let tree = build_spanning_tree(&graph);
    let phi_r = apply_spanning_tree_phi(&graph, &tree, &residuals);
    let o_b_coords: Vec<String> = phi_r.iter().map(ToString::to_string).collect();
    let o_b_is_zero = phi_r.iter().all(BigInt::is_zero);

    // Z -> Q 零性反映検算（E5）。
    let z_to_q_zero_reflection_verified = if spec.compare_to_q {
        let d0_q: Vec<Vec<Rat>> = graph
            .d0
            .iter()
            .map(|r| r.iter().map(|v| Rat::from_int(v.clone())).collect())
            .collect();
        let b_q: Vec<Rat> = graph
            .offsets
            .iter()
            .map(|v| Rat::from_int(v.clone()))
            .collect();
        let q_zero = matches!(
            solve_affine_field(&d0_q, &b_q, graph.vertices.len(), &Rat::zero()),
            Ok(AffineSolutionField::Consistent { .. })
        );
        let z_zero = matches!(
            solve_affine_z(&graph.d0, &graph.offsets, graph.vertices.len()),
            Ok(AffineSolutionZ::Consistent { .. })
        );
        Some(o_b_is_zero == z_zero && z_zero == q_zero)
    } else {
        None
    };

    // 無制約全大域操作 d^0 λ' = b over Z。
    let (unc_exists, unc_particular, unc_h0_rank, unc_reeval) =
        match solve_affine_z(&graph.d0, &graph.offsets, graph.vertices.len()) {
            Ok(AffineSolutionZ::Consistent {
                particular,
                kernel_basis,
                ..
            }) => {
                let reeval = reevaluate_adapter_commutativity(
                    &graph,
                    &particular,
                    &graph.offsets,
                    "unconstrained_global_operation_z",
                );
                (
                    true,
                    Some(vec_to_named_map(&graph.vertices, &particular)),
                    kernel_basis.len(),
                    Some(reeval),
                )
            }
            Ok(AffineSolutionZ::Inconsistent { .. }) => (false, None, 0, None),
            Err(e) => {
                return atlas_undetermined(
                    coeff_domain,
                    point_domain,
                    checks,
                    provenance,
                    map_atlas_alg_err(e),
                );
            }
        };

    let vertex_constrained_repair =
        match solve_vertex_repair_z(&graph, &base_lambdas, &spec.allowed_vertices) {
            Ok(s) => s,
            Err(reason) => {
                return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        };

    let edge_constrained_repair = match solve_edge_repair_z(&graph, &tree, &spec.allowed_edges) {
        Ok(s) => s,
        Err(reason) => {
            return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };

    let refinement = if let Some(ref_spec) = &spec.refinement {
        for clause in [
            MathClause::G142F1,
            MathClause::G142F2,
            MathClause::G142F3,
            MathClause::G142F4,
            MathClause::G142F5,
        ] {
            if !provenance.clauses.contains(&clause) {
                provenance.clauses.push(clause);
            }
        }
        match compute_atlas_refinement(
            spec,
            ref_spec,
            &graph,
            &base_lambdas,
            &tree,
            &phi_r,
            &empty_bindings,
            &expand,
            &|mat, rhs, n_vars| match solve_affine_z(mat, rhs, n_vars).map_err(map_atlas_alg_err)? {
                AffineSolutionZ::Consistent {
                    particular,
                    kernel_basis,
                    ..
                } => Ok((Some(particular), kernel_basis)),
                AffineSolutionZ::Inconsistent { .. } => Ok((None, Vec::new())),
            },
        ) {
            Ok(r) => Some(r),
            Err(reason) => {
                return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        }
    } else {
        None
    };

    let extended_language_non_transport = if let Some(ext) = &spec.extended_language_check {
        if !provenance.clauses.contains(&MathClause::G141H12) {
            provenance.clauses.push(MathClause::G141H12);
        }
        match compute_extended_language_check(ext, BigInt::zero(), &expand) {
            Ok(r) => Some(r),
            Err(reason) => {
                return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        }
    } else {
        None
    };

    let verdict = determine_atlas_verdict(
        o_b_is_zero,
        refinement.as_ref(),
        extended_language_non_transport.as_ref(),
    );

    let detail = AtlasOutcomeDetail {
        coeff_ring_label: "Z".to_owned(),
        num_vertices: graph.vertices.len(),
        num_edges: graph.edges.len(),
        graph_connected: true,
        saga_sign_commutes_verified: saga_ok,
        real_residuals,
        spanning_tree_edges: tree
            .tree_edge_indices
            .iter()
            .map(|&i| graph.edges[i].name.clone())
            .collect(),
        chord_edges: tree
            .chord_edge_indices
            .iter()
            .map(|&i| graph.edges[i].name.clone())
            .collect(),
        designated_class_o_b_coords: o_b_coords.clone(),
        designated_class_kappa_b_coords: o_b_coords,
        o_b_is_zero,
        kappa_b_is_zero: o_b_is_zero,
        diagnostic_h1_rank,
        primitive_relation_connected_verified: prim_rel_ok,
        z_to_q_zero_reflection_verified,
        unconstrained_global_operation_exists: unc_exists,
        unconstrained_particular_lambda: unc_particular,
        unconstrained_h0_torsor_rank: unc_h0_rank,
        unconstrained_reevaluation: unc_reeval,
        vertex_constrained_repair,
        edge_constrained_repair,
        refinement,
        extended_language_non_transport,
    };

    atlas_outcome(verdict, coeff_domain, point_domain, checks, provenance, detail)
}

fn eval_vertex_map<C, FE>(
    vertices: &[String],
    entries: &[(String, PolyExpr)],
    empty_bindings: &ExprBindings,
    expand: &FE,
) -> Result<Vec<C>, SilenceReason>
where
    C: RingCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
{
    let map: BTreeMap<&str, &PolyExpr> = entries.iter().map(|(k, v)| (k.as_str(), v)).collect();
    let mut out = Vec::with_capacity(vertices.len());
    for v in vertices {
        out.push(eval_const_expr(map[v.as_str()], empty_bindings, expand)?);
    }
    Ok(out)
}

pub(crate) fn vec_to_named_map<C: ToString>(names: &[String], vals: &[C]) -> BTreeMap<String, String> {
    names
        .iter()
        .zip(vals)
        .map(|(n, v)| (n.clone(), v.to_string()))
        .collect()
}

fn determine_atlas_verdict(
    o_b_is_zero: bool,
    refinement: Option<&crate::ir::result_phase4::AtlasRefinementResult>,
    ext: Option<&crate::ir::result_phase4::ExtendedLanguageResult>,
) -> Verdict {
    if let Some(e) = ext
        && !e.all_extended_checks_preserved
    {
        return Verdict::Refuted;
    }
    if let Some(r) = refinement
        && (!r.condition_c.all_passed
            || !r.cochain_map_commutes
            || !r.h1_isomorphism
            || !r.repair_fiber_isomorphism_verified)
    {
        return Verdict::Refuted;
    }
    if o_b_is_zero {
        Verdict::Established
    } else {
        Verdict::Refuted
    }
}

pub(crate) fn map_atlas_alg_err(err: AlgebraError) -> SilenceReason {
    match err {
        AlgebraError::UnobservedDependency { slots } => SilenceReason::UnobservedDependency { slots },
        other => SilenceReason::ApplicabilityConditionNotMet {
            condition: "atlas_algebra".to_owned(),
            detail: other.to_string(),
        },
    }
}

fn atlas_outcome(
    verdict: Verdict,
    coeff_domain: CoeffDomain,
    point_domain: PointDomain,
    applicability: Vec<ApplicabilityCheck>,
    provenance: Provenance,
    detail: AtlasOutcomeDetail,
) -> ShigureOutcome {
    ShigureOutcome {
        verdict,
        coeff_domain,
        point_domain,
        applicability,
        provenance,
        residual_ideal: Vec::new(),
        empty_witness: None,
        restored: None,
        interaction: None,
        diagram: None,
        path: None,
        transfer: None,
        robustness: None,
        chevalley: None,
        observations: None,
        lift: None,
        artin: None,
        diagnostics: None,
        atlas: Some(detail),
    }
}

fn atlas_undetermined(
    coeff_domain: CoeffDomain,
    point_domain: PointDomain,
    applicability: Vec<ApplicabilityCheck>,
    provenance: Provenance,
    reason: SilenceReason,
) -> ShigureOutcome {
    ShigureOutcome {
        verdict: Verdict::Undetermined(reason),
        coeff_domain,
        point_domain,
        applicability,
        provenance,
        residual_ideal: Vec::new(),
        empty_witness: None,
        restored: None,
        interaction: None,
        diagram: None,
        path: None,
        transfer: None,
        robustness: None,
        chevalley: None,
        observations: None,
        lift: None,
        artin: None,
        diagnostics: None,
        atlas: None,
    }
}
