//! 有限連結単純グラフ上の実 adapter・SAGA 符号比較・spanning tree $\Phi_R$・
//! 指定診断類 $\kappa_b$・制約付き全修復（$H_V, H_E$）・Atlas 細分化・拡張言語非移送の計算核
//! （G-141 G1–G5・H8・H12 / G-142 E1–E6・F1–F7・W3 / AC6・AC7）。

use crate::algebra::artin::{AffineSolutionField, solve_affine_field};
use crate::algebra::cochain::{CochainComplex, CochainMap, mat_vec};
use crate::algebra::linear::{AffineSolutionZ, smith_normal_form_z, solve_affine_z};
use crate::algebra::poly::{AlgebraError, Poly};
use crate::algebra::poly_expr::ExprBindings;
use crate::algebra::scalar::{FpElem, Rat, RingCoeff};
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
use crate::solver::atlas_refinement::{compute_atlas_refinement, graph_as_z, graph_d0_z};
use crate::solver::atlas_repair::{solve_edge_repair, solve_vertex_repair};
use crate::solver::diagnostics::lift_mat_z_to_q;
use crate::solver::lift_backend::{FieldRingAdapter, FpFieldAdapter, QFieldAdapter};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::collections::BTreeMap;

pub(crate) type JointSolution<C> = (Option<Vec<C>>, Vec<Vec<C>>);

pub(crate) trait AtlasRingBackend {
    type Coeff: RingCoeff;

    fn zero(&self) -> Self::Coeff;
    fn coeff_label(&self) -> String;
    fn expand_expr(
        &self,
        expr: &PolyExpr,
        bindings: &ExprBindings,
    ) -> Result<Poly<Self::Coeff>, AlgebraError>;
    fn solve_affine(
        &self,
        mat: &[Vec<Self::Coeff>],
        rhs: &[Self::Coeff],
        cols: usize,
    ) -> Result<JointSolution<Self::Coeff>, SilenceReason>;
    fn check_h0_h1_isomorphism(
        &self,
        coarse: &EvaluatedGraph<Self::Coeff>,
        fine: &EvaluatedGraph<Self::Coeff>,
        p0_z: &[Vec<BigInt>],
        p1_z: &[Vec<BigInt>],
    ) -> Result<(bool, bool), SilenceReason>;
    fn reeval_suffix(&self) -> &'static str;
    fn inconsistent_edge_repair_detail(&self) -> &'static str;
    fn is_unit(&self, val: &Self::Coeff) -> bool;
    fn compute_z_to_q_reflection(
        &self,
        spec: &AtlasTaskSpec,
        graph: &EvaluatedGraph<Self::Coeff>,
        o_b_is_zero: bool,
    ) -> Result<Option<bool>, SilenceReason>;
}

struct FieldAtlasBackend<A: FieldRingAdapter>(A);

impl<A: FieldRingAdapter> AtlasRingBackend for FieldAtlasBackend<A> {
    type Coeff = A::Coeff;

    fn zero(&self) -> Self::Coeff {
        self.0.zero()
    }

    fn coeff_label(&self) -> String {
        self.0.coeff_label()
    }

    fn expand_expr(
        &self,
        expr: &PolyExpr,
        bindings: &ExprBindings,
    ) -> Result<Poly<Self::Coeff>, AlgebraError> {
        self.0.expand_expr(expr, bindings)
    }

    fn solve_affine(
        &self,
        mat: &[Vec<Self::Coeff>],
        rhs: &[Self::Coeff],
        cols: usize,
    ) -> Result<JointSolution<Self::Coeff>, SilenceReason> {
        match solve_affine_field(mat, rhs, cols, &self.0.zero()).map_err(map_atlas_alg_err)? {
            AffineSolutionField::Consistent {
                particular,
                kernel_basis,
                ..
            } => Ok((Some(particular), kernel_basis)),
            AffineSolutionField::Inconsistent { .. } => Ok((None, Vec::new())),
        }
    }

    fn check_h0_h1_isomorphism(
        &self,
        coarse: &EvaluatedGraph<Self::Coeff>,
        fine: &EvaluatedGraph<Self::Coeff>,
        p0_z: &[Vec<BigInt>],
        p1_z: &[Vec<BigInt>],
    ) -> Result<(bool, bool), SilenceReason> {
        let d0_c_z = graph_d0_z(coarse);
        let d0_f_z = graph_d0_z(fine);
        let zero = self.0.zero();
        let cpx_c = CochainComplex::new(
            coarse.vertices.len(),
            coarse.edges.len(),
            0,
            self.0.lift_mat_z(&d0_c_z),
            Vec::new(),
            zero.clone(),
        )
        .map_err(map_atlas_alg_err)?;
        let cpx_f = CochainComplex::new(
            fine.vertices.len(),
            fine.edges.len(),
            0,
            self.0.lift_mat_z(&d0_f_z),
            Vec::new(),
            zero,
        )
        .map_err(map_atlas_alg_err)?;
        let map = CochainMap::new(
            &cpx_c,
            &cpx_f,
            self.0.lift_mat_z(p0_z),
            self.0.lift_mat_z(p1_z),
            Vec::new(),
        )
        .map_err(map_atlas_alg_err)?;
        let ind = map
            .induced_field(&cpx_c, &cpx_f)
            .map_err(map_atlas_alg_err)?;
        Ok((ind.h0.isomorphism, ind.h1.isomorphism))
    }

    fn reeval_suffix(&self) -> &'static str {
        ""
    }

    fn inconsistent_edge_repair_detail(&self) -> &'static str {
        "repaired offset b + delta_b did not admit a global operation"
    }

    fn is_unit(&self, val: &Self::Coeff) -> bool {
        !val.coeff_is_zero()
    }

    fn compute_z_to_q_reflection(
        &self,
        _spec: &AtlasTaskSpec,
        _graph: &EvaluatedGraph<Self::Coeff>,
        _o_b_is_zero: bool,
    ) -> Result<Option<bool>, SilenceReason> {
        Ok(None)
    }
}

struct ZAtlasBackend;

impl AtlasRingBackend for ZAtlasBackend {
    type Coeff = BigInt;

    fn zero(&self) -> BigInt {
        BigInt::zero()
    }

    fn coeff_label(&self) -> String {
        "Z".to_owned()
    }

    fn expand_expr(
        &self,
        expr: &PolyExpr,
        bindings: &ExprBindings,
    ) -> Result<Poly<BigInt>, AlgebraError> {
        Poly::from_expr_z(expr, bindings)
    }

    fn solve_affine(
        &self,
        mat: &[Vec<BigInt>],
        rhs: &[BigInt],
        cols: usize,
    ) -> Result<JointSolution<BigInt>, SilenceReason> {
        match solve_affine_z(mat, rhs, cols).map_err(map_atlas_alg_err)? {
            AffineSolutionZ::Consistent {
                particular,
                kernel_basis,
                ..
            } => Ok((Some(particular), kernel_basis)),
            AffineSolutionZ::Inconsistent { .. } => Ok((None, Vec::new())),
        }
    }

    fn check_h0_h1_isomorphism(
        &self,
        coarse: &EvaluatedGraph<BigInt>,
        fine: &EvaluatedGraph<BigInt>,
        p0_z: &[Vec<BigInt>],
        p1_z: &[Vec<BigInt>],
    ) -> Result<(bool, bool), SilenceReason> {
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

    fn reeval_suffix(&self) -> &'static str {
        "_z"
    }

    fn inconsistent_edge_repair_detail(&self) -> &'static str {
        "repaired offset b + delta_b did not admit an integer global operation"
    }

    fn is_unit(&self, val: &BigInt) -> bool {
        *val == BigInt::one() || *val == -BigInt::one()
    }

    fn compute_z_to_q_reflection(
        &self,
        spec: &AtlasTaskSpec,
        graph: &EvaluatedGraph<BigInt>,
        o_b_is_zero: bool,
    ) -> Result<Option<bool>, SilenceReason> {
        if !spec.compare_to_q {
            return Ok(None);
        }
        let d0_q = lift_mat_z_to_q(&graph.d0);
        let b_q: Vec<Rat> = graph
            .offsets
            .iter()
            .map(|v| Rat::from_int(v.clone()))
            .collect();
        let q_zero = match solve_affine_field(&d0_q, &b_q, graph.vertices.len(), &Rat::zero()) {
            Ok(AffineSolutionField::Consistent { .. }) => true,
            Ok(AffineSolutionField::Inconsistent { .. }) => false,
            Err(e) => return Err(map_atlas_alg_err(e)),
        };
        let z_zero = match solve_affine_z(&graph.d0, &graph.offsets, graph.vertices.len()) {
            Ok(AffineSolutionZ::Consistent { .. }) => true,
            Ok(AffineSolutionZ::Inconsistent { .. }) => false,
            Err(e) => return Err(map_atlas_alg_err(e)),
        };
        Ok(Some(o_b_is_zero == z_zero && z_zero == q_zero))
    }
}

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
        CoeffDomain::Q => {
            solve_atlas_with_backend(&FieldAtlasBackend(QFieldAdapter), spec, checks, provenance)
        }
        CoeffDomain::Fp(p) => {
            let zero_fp = FpElem::from_checked_prime(BigInt::zero(), p.clone());
            solve_atlas_with_backend(
                &FieldAtlasBackend(FpFieldAdapter {
                    p: p.clone(),
                    zero_fp,
                }),
                spec,
                checks,
                provenance,
            )
        }
        CoeffDomain::Z => solve_atlas_with_backend(&ZAtlasBackend, spec, checks, provenance),
    }
}

fn solve_atlas_with_backend<B: AtlasRingBackend>(
    backend: &B,
    spec: &AtlasTaskSpec,
    mut checks: Vec<ApplicabilityCheck>,
    mut provenance: Provenance,
) -> ShigureOutcome {
    let coeff_domain = spec.coeff_domain.clone();
    let point_domain = PointDomain::UniversalRing;
    let zero = backend.zero();
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
    let expand = |e: &PolyExpr, b: &ExprBindings| backend.expand_expr(e, b);

    // mu の評価（Unobserved 検出を含む）。
    if let Err(reason) = eval_const_expr(&spec.mu, &empty_bindings, &expand) {
        return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
    }

    let graph = match build_evaluated_graph(
        &spec.vertices,
        &spec.edges,
        zero.clone(),
        &empty_bindings,
        &expand,
    ) {
        Ok(g) => g,
        Err(reason) => {
            return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };

    let base_lambdas =
        match eval_vertex_map(&spec.vertices, &spec.base_lambdas, &empty_bindings, &expand) {
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
    let residuals: Vec<B::Coeff> = d0_lam
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

    let z_to_q_zero_reflection_verified =
        match backend.compute_z_to_q_reflection(spec, &graph, o_b_is_zero) {
            Ok(v) => v,
            Err(reason) => {
                return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        };

    // 無制約全大域操作 d^0 λ' = b。
    let unc_label = format!("unconstrained_global_operation{}", backend.reeval_suffix());
    let (unc_exists, unc_particular, unc_h0_rank, unc_reeval) =
        match backend.solve_affine(&graph.d0, &graph.offsets, graph.vertices.len()) {
            Ok((Some(particular), kernel_basis)) => {
                let reeval = reevaluate_adapter_commutativity(
                    &graph,
                    &particular,
                    &graph.offsets,
                    &unc_label,
                );
                let map = vec_to_named_map(&graph.vertices, &particular);
                (true, Some(map), kernel_basis.len(), Some(reeval))
            }
            Ok((None, _)) => (false, None, 0, None),
            Err(reason) => {
                return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        };

    // 頂点許容修復 H_V: d^0|_{H_V} a = b - d^0 λ。
    let vertex_constrained_repair =
        match solve_vertex_repair(backend, &graph, &base_lambdas, &spec.allowed_vertices) {
            Ok(s) => s,
            Err(reason) => {
                return atlas_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        };

    // 辺許容修復 H_E: Φ_R(Δb|_{H_E}) = -Φ_R(b)。
    let edge_constrained_repair =
        match solve_edge_repair(backend, &graph, &tree, &spec.allowed_edges) {
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
            backend,
            spec,
            ref_spec,
            &graph,
            &base_lambdas,
            &empty_bindings,
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
        match compute_extended_language_check(ext, zero, &expand) {
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
        coeff_ring_label: backend.coeff_label(),
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

    atlas_outcome(
        verdict,
        coeff_domain,
        point_domain,
        checks,
        provenance,
        detail,
    )
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

pub(crate) fn vec_to_named_map<C: ToString>(
    names: &[String],
    vals: &[C],
) -> BTreeMap<String, String> {
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
        && (!e.all_atomic_ops_commute || !e.all_extended_checks_preserved)
    {
        return Verdict::Refuted;
    }
    if let Some(r) = refinement
        && (!r.condition_c.all_passed
            || !r.cochain_map_commutes
            || !r.h0_isomorphism
            || !r.h1_isomorphism
            || !r.designated_o_preserved
            || !r.designated_kappa_preserved
            || !r.repair_fiber_isomorphism_verified
            || !r.inverse_reconstruction_verified
            || r.eval_condition_fiber_preserved == Some(false))
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
        AlgebraError::UnobservedDependency { slots } => {
            SilenceReason::UnobservedDependency { slots }
        }
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
        occurrence: None,
        partial: None,
        revision: None,
        multisource: None,
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
        occurrence: None,
        partial: None,
        revision: None,
        multisource: None,
    }
}
