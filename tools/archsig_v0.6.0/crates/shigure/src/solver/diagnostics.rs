//! 整数診断複体 $C_\Lambda$・Law 値別分解・係数変更・診断層 $B_\pi$・
//! 値合流 Mayer–Vietoris・診断次元実現の計算核（G-142 A–D・W1–W2 / AC5・AC7）。

use crate::algebra::cochain::{CochainComplex, CohomologyGroup};
use crate::algebra::scalar::{FpElem, Rat};
use crate::algebra::syzygy::FieldCoeff;
use crate::ir::change::PointDomain;
use crate::ir::diagnostics::{
    CheckedDiagnosticsTask, DiagnosticsReadoutSpec, DiagnosticsTaskSpec, SupportedNerveSpec,
};
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{ApplicabilityCheck, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_phase4::{DiagnosticsOutcomeDetail, LawValueBlockSummary};
use crate::ir::term::{CoeffDomain, ScalarLit};
use crate::solver::diagnostics_change::compute_coeff_change;
use crate::solver::diagnostics_collision::{
    compute_collision_mv, compute_dimension_realization,
};
use crate::solver::diagnostics_strat::{
    compute_polynomial_stratification, compute_r_point_contrast, detect_upper_semicontinuity,
};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::collections::{BTreeMap, BTreeSet};

/// 交差支持を計算済みの K1 `TargetSupportedNerve`。
#[derive(Clone, Debug)]
pub(crate) struct ComputedNerve {
    pub(crate) chart_names: Vec<String>,
    pub(crate) chart_supports: Vec<BTreeSet<String>>,
    pub(crate) edges: Vec<ComputedNerveEdge>,
    pub(crate) faces: Vec<ComputedNerveFace>,
}

#[derive(Clone, Debug)]
pub(crate) struct ComputedNerveEdge {
    pub(crate) left_idx: usize,
    pub(crate) right_idx: usize,
    pub(crate) support: BTreeSet<String>,
}

#[derive(Clone, Debug)]
pub(crate) struct ComputedNerveFace {
    pub(crate) e0_idx: usize,
    pub(crate) e1_idx: usize,
    pub(crate) e2_idx: usize,
    pub(crate) support: BTreeSet<String>,
}

/// セル次数ごとの `(law_name, value_label)` 座標系と整数微分行列（0, 1, -1）。
#[derive(Clone, Debug)]
pub(crate) struct DiagnosticComplexData {
    pub(crate) coords0: Vec<(usize, String, String)>,
    pub(crate) coords1: Vec<(usize, String, String)>,
    pub(crate) coords2: Vec<(usize, String, String)>,
    pub(crate) d0_z: Vec<Vec<BigInt>>,
    pub(crate) d1_z: Vec<Vec<BigInt>>,
}

/// 任意の診断係数環 `Λ ∈ {Z, Q, F_p}` 上のコホモロジー要約。
#[derive(Clone, Debug)]
pub(crate) struct DiagCohomologySummary {
    pub(crate) d1_d0_zero_verified: bool,
    pub(crate) h0_summary: String,
    pub(crate) h1_summary: String,
    pub(crate) h2_summary: String,
    pub(crate) h0_free_rank: usize,
    pub(crate) h1_free_rank: usize,
    pub(crate) h1_torsion: Vec<String>,
    pub(crate) h2_free_rank: usize,
}

/// `CheckedDiagnosticsTask` を実行し、診断複体・係数変更・層別・合流・次元実現を返す。
pub fn solve_diagnostics_task(task: &CheckedDiagnosticsTask) -> ShigureOutcome {
    let spec = task.spec();
    let coeff_domain = spec.diagnostic_coeff.clone();
    let point_domain = match &spec.readout {
        DiagnosticsReadoutSpec::Static { .. } => PointDomain::UniversalRing,
        DiagnosticsReadoutSpec::Polynomial { .. } => PointDomain::AlgebraicClosure,
    };
    let mut provenance = spec.provenance.clone();
    for clause in [
        MathClause::G142A1,
        MathClause::G142A2,
        MathClause::G142A3,
        MathClause::G142C1,
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
            "diagnostic_coeff_valid",
            MathClause::G142A1,
            detail.clone(),
        ));
        return diag_undetermined(
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
        "diagnostic_coeff_valid",
        MathClause::G142A1,
    ));

    let nerve = match compute_nerve(&spec.nerve) {
        Ok(n) => {
            checks.push(ApplicabilityCheck::passed(
                "k1_supported_nerve_valid",
                MathClause::G142A1,
            ));
            n
        }
        Err(reason) => {
            checks.push(ApplicabilityCheck::failed(
                "k1_supported_nerve_valid",
                MathClause::G142A1,
                reason.code(),
            ));
            return diag_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };

    match &spec.readout {
        DiagnosticsReadoutSpec::Static {
            sources,
            reading,
            laws,
            ..
        } => solve_static_diagnostics(
            spec,
            &nerve,
            sources,
            reading,
            laws,
            coeff_domain,
            point_domain,
            checks,
            provenance,
        ),
        DiagnosticsReadoutSpec::Polynomial { .. } => solve_polynomial_diagnostics(
            spec,
            &nerve,
            coeff_domain,
            point_domain,
            checks,
            provenance,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn solve_static_diagnostics(
    spec: &DiagnosticsTaskSpec,
    nerve: &ComputedNerve,
    _sources: &[String],
    reading: &[(String, String)],
    laws: &[crate::ir::diagnostics::StaticLawReadoutSpec],
    coeff_domain: CoeffDomain,
    point_domain: PointDomain,
    mut checks: Vec<ApplicabilityCheck>,
    provenance: Provenance,
) -> ShigureOutcome {
    let reading_map: BTreeMap<&str, &str> = reading
        .iter()
        .map(|(s, t)| (s.as_str(), t.as_str()))
        .collect();

    // Adequacy 検査: q(x) == q(y) => eval_l(x) == eval_l(y)
    let mut target_law_values: BTreeMap<String, BTreeMap<String, String>> = BTreeMap::new();
    let mut target_law_lits: BTreeMap<String, BTreeMap<String, ScalarLit>> = BTreeMap::new();
    for law in laws {
        let mut by_target: BTreeMap<String, ScalarLit> = BTreeMap::new();
        for (src, lit) in &law.values {
            let tgt = reading_map[src.as_str()].to_owned();
            if let Some(prev) = by_target.get(&tgt) {
                if prev != lit {
                    checks.push(ApplicabilityCheck::failed(
                        "reading_adequacy",
                        MathClause::G142A1,
                        format!(
                            "law `{}` assigns distinct values `{prev}` and `{lit}` to target `{tgt}`",
                            law.law_name
                        ),
                    ));
                    return diag_undetermined(
                        coeff_domain,
                        point_domain,
                        checks,
                        provenance,
                        SilenceReason::ApplicabilityConditionNotMet {
                            condition: "reading_adequacy".to_owned(),
                            detail: format!(
                                "reading q is not adequate for law `{}` at target `{tgt}`: `{prev}` != `{lit}`",
                                law.law_name
                            ),
                        },
                    );
                }
            } else {
                by_target.insert(tgt, lit.clone());
            }
        }
        let str_map: BTreeMap<String, String> = by_target
            .iter()
            .map(|(t, lit)| (t.clone(), lit.to_string()))
            .collect();
        target_law_values.insert(law.law_name.clone(), str_map);
        target_law_lits.insert(law.law_name.clone(), by_target);
    }
    checks.push(ApplicabilityCheck::passed(
        "reading_adequacy",
        MathClause::G142A1,
    ));

    let complex_data = build_diagnostic_complex(nerve, &target_law_values);
    let summary = match evaluate_complex_over_domain(&complex_data, &coeff_domain) {
        Ok(s) => s,
        Err(reason) => {
            return diag_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };
    checks.push(ApplicabilityCheck::passed(
        "cochain_d1_d0_zero",
        MathClause::G142A1,
    ));

    let block_decomposition =
        match compute_block_decomposition(nerve, &target_law_values, &coeff_domain) {
            Ok(b) => b,
            Err(reason) => {
                return diag_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        };

    let coeff_change = if let Some(cc) = &spec.coeff_change {
        match compute_coeff_change(
            &coeff_domain,
            cc,
            nerve,
            &complex_data,
            Some(&target_law_lits),
            &mut checks,
        ) {
            Ok(res) => Some(res),
            Err(reason) => {
                return diag_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        }
    } else {
        None
    };

    let mut collisions = Vec::new();
    for col in &spec.collisions {
        match compute_collision_mv(col, nerve, Some(&reading_map), &coeff_domain) {
            Ok(res) => collisions.push(res),
            Err(reason) => {
                return diag_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        }
    }

    let dimension_realization = if let Some(dr) = &spec.dimension_realization {
        match compute_dimension_realization(dr, &coeff_domain) {
            Ok(res) => Some(res),
            Err(reason) => {
                return diag_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        }
    } else {
        None
    };

    let detail = DiagnosticsOutcomeDetail {
        diagnostic_coeff_label: coeff_domain.to_string(),
        reading_adequate: true,
        d1_d0_zero_verified: summary.d1_d0_zero_verified,
        cell_dims: [
            complex_data.coords0.len(),
            complex_data.coords1.len(),
            complex_data.coords2.len(),
        ],
        h0_summary: summary.h0_summary,
        h1_summary: summary.h1_summary,
        h2_summary: summary.h2_summary,
        h0_free_rank: summary.h0_free_rank,
        h1_free_rank: summary.h1_free_rank,
        h1_torsion: summary.h1_torsion,
        h2_free_rank: summary.h2_free_rank,
        block_decomposition,
        coeff_change,
        strata: Vec::new(),
        collisions,
        upper_semicontinuity_refutation: None,
        r_point_contrast: None,
        dimension_realization,
    };

    diag_outcome(
        Verdict::Established,
        coeff_domain,
        point_domain,
        checks,
        provenance,
        detail,
    )
}

fn solve_polynomial_diagnostics(
    spec: &DiagnosticsTaskSpec,
    nerve: &ComputedNerve,
    coeff_domain: CoeffDomain,
    point_domain: PointDomain,
    mut checks: Vec<ApplicabilityCheck>,
    mut provenance: Provenance,
) -> ShigureOutcome {
    for clause in [
        MathClause::G142B1,
        MathClause::G142B2,
        MathClause::G142B3,
        MathClause::G142B5,
        MathClause::G142C2,
        MathClause::G142C3,
    ] {
        if !provenance.clauses.contains(&clause) {
            provenance.clauses.push(clause);
        }
    }

    let strat_out = match compute_polynomial_stratification(spec, nerve, &coeff_domain) {
        Ok(s) => {
            checks.push(ApplicabilityCheck::passed(
                "polynomial_partition_stratification",
                MathClause::G142B5,
            ));
            s
        }
        Err(reason) => {
            checks.push(ApplicabilityCheck::failed(
                "polynomial_partition_stratification",
                MathClause::G142B5,
                reason.code(),
            ));
            return diag_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };

    let upper_refutation = match detect_upper_semicontinuity(&strat_out) {
        Ok(r) => {
            if r.is_some() && !provenance.clauses.contains(&MathClause::G142D3) {
                provenance.clauses.push(MathClause::G142D3);
            }
            r
        }
        Err(reason) => {
            return diag_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };

    let r_point_contrast = if let Some(rp) = &spec.r_point_probe {
        match compute_r_point_contrast(spec, rp, nerve, &coeff_domain) {
            Ok(res) => Some(res),
            Err(reason) => {
                return diag_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        }
    } else {
        None
    };

    let mut collisions = Vec::new();
    for col in &spec.collisions {
        match compute_collision_mv(col, nerve, None, &coeff_domain) {
            Ok(res) => collisions.push(res),
            Err(reason) => {
                return diag_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        }
    }

    let dimension_realization = if let Some(dr) = &spec.dimension_realization {
        match compute_dimension_realization(dr, &coeff_domain) {
            Ok(res) => Some(res),
            Err(reason) => {
                return diag_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        }
    } else {
        None
    };

    let coeff_change = if let Some(cc) = &spec.coeff_change {
        match compute_coeff_change(
            &coeff_domain,
            cc,
            nerve,
            &strat_out.generic_complex,
            None,
            &mut checks,
        ) {
            Ok(res) => Some(res),
            Err(reason) => {
                return diag_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        }
    } else {
        None
    };

    let detail = DiagnosticsOutcomeDetail {
        diagnostic_coeff_label: coeff_domain.to_string(),
        reading_adequate: true,
        d1_d0_zero_verified: strat_out.generic_summary.d1_d0_zero_verified,
        cell_dims: [
            strat_out.generic_complex.coords0.len(),
            strat_out.generic_complex.coords1.len(),
            strat_out.generic_complex.coords2.len(),
        ],
        h0_summary: strat_out.generic_summary.h0_summary,
        h1_summary: strat_out.generic_summary.h1_summary,
        h2_summary: strat_out.generic_summary.h2_summary,
        h0_free_rank: strat_out.generic_summary.h0_free_rank,
        h1_free_rank: strat_out.generic_summary.h1_free_rank,
        h1_torsion: strat_out.generic_summary.h1_torsion,
        h2_free_rank: strat_out.generic_summary.h2_free_rank,
        block_decomposition: strat_out.generic_blocks,
        coeff_change,
        strata: strat_out.strata,
        collisions,
        upper_semicontinuity_refutation: upper_refutation,
        r_point_contrast,
        dimension_realization,
    };

    diag_outcome(
        Verdict::Established,
        coeff_domain,
        point_domain,
        checks,
        provenance,
        detail,
    )
}

/// K1 nerve の交差支持（edge = S_left ∩ S_right, face = S_e0 ∩ S_e1 ∩ S_e2）を計算する。
pub(crate) fn compute_nerve(spec: &SupportedNerveSpec) -> Result<ComputedNerve, SilenceReason> {
    let mut chart_idx: BTreeMap<&str, usize> = BTreeMap::new();
    let mut chart_names = Vec::with_capacity(spec.charts.len());
    let mut chart_supports = Vec::with_capacity(spec.charts.len());
    for (i, ch) in spec.charts.iter().enumerate() {
        chart_idx.insert(ch.name.as_str(), i);
        chart_names.push(ch.name.clone());
        chart_supports.push(ch.support.iter().cloned().collect::<BTreeSet<String>>());
    }

    let mut edge_idx: BTreeMap<&str, usize> = BTreeMap::new();
    let mut edges = Vec::with_capacity(spec.edges.len());
    for (i, e) in spec.edges.iter().enumerate() {
        let Some(&l) = chart_idx.get(e.left.as_str()) else {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "nerve_edge_endpoint".to_owned(),
                detail: format!("unknown left chart `{}`", e.left),
            });
        };
        let Some(&r) = chart_idx.get(e.right.as_str()) else {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "nerve_edge_endpoint".to_owned(),
                detail: format!("unknown right chart `{}`", e.right),
            });
        };
        let support: BTreeSet<String> = chart_supports[l]
            .intersection(&chart_supports[r])
            .cloned()
            .collect();
        edge_idx.insert(e.name.as_str(), i);
        edges.push(ComputedNerveEdge {
            left_idx: l,
            right_idx: r,
            support,
        });
    }

    let mut faces = Vec::with_capacity(spec.faces.len());
    for f in &spec.faces {
        let (Some(&e0), Some(&e1), Some(&e2)) = (
            edge_idx.get(f.e0.as_str()),
            edge_idx.get(f.e1.as_str()),
            edge_idx.get(f.e2.as_str()),
        ) else {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "nerve_face_edges".to_owned(),
                detail: format!("unknown edge in face `{}`", f.name),
            });
        };
        let support: BTreeSet<String> = edges[e0]
            .support
            .intersection(&edges[e1].support)
            .filter(|t| edges[e2].support.contains(*t))
            .cloned()
            .collect();
        faces.push(ComputedNerveFace {
            e0_idx: e0,
            e1_idx: e1,
            e2_idx: e2,
            support,
        });
    }

    Ok(ComputedNerve {
        chart_names,
        chart_supports,
        edges,
        faces,
    })
}

/// 任意の target ごとの `(law_name -> value_label)` 割当てから K0/K1 診断複体（整数行列）を構築する（A1）。
pub(crate) fn build_diagnostic_complex(
    nerve: &ComputedNerve,
    target_law_values: &BTreeMap<String, BTreeMap<String, String>>,
) -> DiagnosticComplexData {
    let mut coords0 = Vec::new();
    let mut idx0: BTreeMap<(usize, String, String), usize> = BTreeMap::new();
    for (ci, sup) in nerve.chart_supports.iter().enumerate() {
        for (law_name, val_map) in target_law_values {
            let mut vals = BTreeSet::new();
            for t in sup {
                if let Some(v) = val_map.get(t) {
                    vals.insert(v.clone());
                }
            }
            for v in vals {
                let key = (ci, law_name.clone(), v);
                idx0.insert(key.clone(), coords0.len());
                coords0.push(key);
            }
        }
    }

    let mut coords1 = Vec::new();
    let mut idx1: BTreeMap<(usize, String, String), usize> = BTreeMap::new();
    for (ei, edge) in nerve.edges.iter().enumerate() {
        for (law_name, val_map) in target_law_values {
            let mut vals = BTreeSet::new();
            for t in &edge.support {
                if let Some(v) = val_map.get(t) {
                    vals.insert(v.clone());
                }
            }
            for v in vals {
                let key = (ei, law_name.clone(), v);
                idx1.insert(key.clone(), coords1.len());
                coords1.push(key);
            }
        }
    }

    let mut coords2 = Vec::new();
    for (fi, face) in nerve.faces.iter().enumerate() {
        for (law_name, val_map) in target_law_values {
            let mut vals = BTreeSet::new();
            for t in &face.support {
                if let Some(v) = val_map.get(t) {
                    vals.insert(v.clone());
                }
            }
            for v in vals {
                coords2.push((fi, law_name.clone(), v));
            }
        }
    }

    let dim0 = coords0.len();
    let dim1 = coords1.len();
    let dim2 = coords2.len();
    let mut d0_z = vec![vec![BigInt::zero(); dim0]; dim1];
    for (row, (ei, law, val)) in coords1.iter().enumerate() {
        let edge = &nerve.edges[*ei];
        if let Some(&r_col) = idx0.get(&(edge.right_idx, law.clone(), val.clone())) {
            d0_z[row][r_col] += BigInt::one();
        }
        if let Some(&l_col) = idx0.get(&(edge.left_idx, law.clone(), val.clone())) {
            d0_z[row][l_col] -= BigInt::one();
        }
    }

    let mut d1_z = vec![vec![BigInt::zero(); dim1]; dim2];
    for (row, (fi, law, val)) in coords2.iter().enumerate() {
        let face = &nerve.faces[*fi];
        if let Some(&c0) = idx1.get(&(face.e0_idx, law.clone(), val.clone())) {
            d1_z[row][c0] += BigInt::one();
        }
        if let Some(&c1) = idx1.get(&(face.e1_idx, law.clone(), val.clone())) {
            d1_z[row][c1] -= BigInt::one();
        }
        if let Some(&c2) = idx1.get(&(face.e2_idx, law.clone(), val.clone())) {
            d1_z[row][c2] += BigInt::one();
        }
    }

    DiagnosticComplexData {
        coords0,
        coords1,
        coords2,
        d0_z,
        d1_z,
    }
}

pub(crate) type BlockComplexRaw = (
    Vec<usize>,
    Vec<usize>,
    Vec<usize>,
    Vec<Vec<BigInt>>,
    Vec<Vec<BigInt>>,
);

/// 単一 Law 値 block `K_a` 上の診断部分複体（C1）を整数行列として構築する。
pub(crate) fn build_block_complex(
    nerve: &ComputedNerve,
    active_targets: &BTreeSet<String>,
) -> BlockComplexRaw {
    let mut charts = Vec::new();
    let mut c_pos = BTreeMap::new();
    for (ci, sup) in nerve.chart_supports.iter().enumerate() {
        if sup.iter().any(|t| active_targets.contains(t)) {
            c_pos.insert(ci, charts.len());
            charts.push(ci);
        }
    }
    let mut edges = Vec::new();
    let mut e_pos = BTreeMap::new();
    for (ei, edge) in nerve.edges.iter().enumerate() {
        if edge.support.iter().any(|t| active_targets.contains(t)) {
            e_pos.insert(ei, edges.len());
            edges.push(ei);
        }
    }
    let mut faces = Vec::new();
    for (fi, face) in nerve.faces.iter().enumerate() {
        if face.support.iter().any(|t| active_targets.contains(t)) {
            faces.push(fi);
        }
    }
    let mut d0 = vec![vec![BigInt::zero(); charts.len()]; edges.len()];
    for (row, &ei) in edges.iter().enumerate() {
        let edge = &nerve.edges[ei];
        if let Some(&r_col) = c_pos.get(&edge.right_idx) {
            d0[row][r_col] += BigInt::one();
        }
        if let Some(&l_col) = c_pos.get(&edge.left_idx) {
            d0[row][l_col] -= BigInt::one();
        }
    }
    let mut d1 = vec![vec![BigInt::zero(); edges.len()]; faces.len()];
    for (row, &fi) in faces.iter().enumerate() {
        let face = &nerve.faces[fi];
        if let Some(&c0) = e_pos.get(&face.e0_idx) {
            d1[row][c0] += BigInt::one();
        }
        if let Some(&c1) = e_pos.get(&face.e1_idx) {
            d1[row][c1] -= BigInt::one();
        }
        if let Some(&c2) = e_pos.get(&face.e2_idx) {
            d1[row][c2] += BigInt::one();
        }
    }
    (charts, edges, faces, d0, d1)
}

/// C1: Law 値別部分複体分解 `C^\bullet \cong \bigoplus_{\ell, a} C^\bullet(K_{\ell, a}; \Lambda)` を計算する。
pub(crate) fn compute_block_decomposition(
    nerve: &ComputedNerve,
    target_law_values: &BTreeMap<String, BTreeMap<String, String>>,
    domain: &CoeffDomain,
) -> Result<Vec<LawValueBlockSummary>, SilenceReason> {
    let mut out = Vec::new();
    for (law_name, val_map) in target_law_values {
        let mut by_val: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for (tgt, val) in val_map {
            by_val.entry(val.clone()).or_default().insert(tgt.clone());
        }
        for (val_label, targets) in by_val {
            let (c, e, f, d0, d1) = build_block_complex(nerve, &targets);
            let data = DiagnosticComplexData {
                coords0: c.iter().map(|&i| (i, law_name.clone(), val_label.clone())).collect(),
                coords1: e.iter().map(|&i| (i, law_name.clone(), val_label.clone())).collect(),
                coords2: f.iter().map(|&i| (i, law_name.clone(), val_label.clone())).collect(),
                d0_z: d0,
                d1_z: d1,
            };
            let sum = evaluate_complex_over_domain(&data, domain)?;
            out.push(LawValueBlockSummary {
                law_name: law_name.clone(),
                value_label: val_label,
                cell_dims: [c.len(), e.len(), f.len()],
                h0_free_rank: sum.h0_free_rank,
                h1_free_rank: sum.h1_free_rank,
                h1_torsion: sum.h1_torsion,
            });
        }
    }
    Ok(out)
}

/// 整数行列複体を指定診断係数環 `Λ` へ写して `d^1 d^0 == 0` と `H^0, H^1, H^2` を計算する。
pub(crate) fn evaluate_complex_over_domain(
    data: &DiagnosticComplexData,
    domain: &CoeffDomain,
) -> Result<DiagCohomologySummary, SilenceReason> {
    let dim0 = data.coords0.len();
    let dim1 = data.coords1.len();
    let dim2 = data.coords2.len();
    match domain {
        CoeffDomain::Z => {
            let cpx = CochainComplex::new(
                dim0,
                dim1,
                dim2,
                data.d0_z.clone(),
                data.d1_z.clone(),
                BigInt::zero(),
            )
            .map_err(map_diag_alg_err)?;
            let coh = cpx.cohomology_z().map_err(map_diag_alg_err)?;
            Ok(DiagCohomologySummary {
                d1_d0_zero_verified: true,
                h0_summary: coh.h0.display("Z"),
                h1_summary: coh.h1.display("Z"),
                h2_summary: coh.h2.display("Z"),
                h0_free_rank: coh.h0.free_rank,
                h1_free_rank: coh.h1.free_rank,
                h1_torsion: coh
                    .h1
                    .torsion_invariants
                    .iter()
                    .map(ToString::to_string)
                    .collect(),
                h2_free_rank: coh.h2.free_rank,
            })
        }
        CoeffDomain::Q => {
            let d0 = lift_mat_z_to_q(&data.d0_z);
            let d1 = lift_mat_z_to_q(&data.d1_z);
            evaluate_field_complex(dim0, dim1, dim2, d0, d1, Rat::zero(), "Q")
        }
        CoeffDomain::Fp(p) => {
            let Some(zero_fp) = FpElem::zero(p.clone()) else {
                return Err(SilenceReason::UnsupportedCoeffRing {
                    domain: domain.clone(),
                    detail: format!("modulus {p} is not prime"),
                });
            };
            let d0 = lift_mat_z_to_fp(&data.d0_z, p);
            let d1 = lift_mat_z_to_fp(&data.d1_z, p);
            let label = format!("F_{p}");
            evaluate_field_complex(dim0, dim1, dim2, d0, d1, zero_fp, &label)
        }
    }
}

fn evaluate_field_complex<C: FieldCoeff>(
    dim0: usize,
    dim1: usize,
    dim2: usize,
    d0: Vec<Vec<C>>,
    d1: Vec<Vec<C>>,
    zero: C,
    ring_label: &str,
) -> Result<DiagCohomologySummary, SilenceReason> {
    let cpx = CochainComplex::new(dim0, dim1, dim2, d0, d1, zero).map_err(map_diag_alg_err)?;
    let coh = cpx.cohomology_field().map_err(map_diag_alg_err)?;
    Ok(DiagCohomologySummary {
        d1_d0_zero_verified: true,
        h0_summary: CohomologyGroup::free(coh.h0_dim).display(ring_label),
        h1_summary: CohomologyGroup::free(coh.h1_dim).display(ring_label),
        h2_summary: CohomologyGroup::free(coh.h2_dim).display(ring_label),
        h0_free_rank: coh.h0_dim,
        h1_free_rank: coh.h1_dim,
        h1_torsion: Vec::new(),
        h2_free_rank: coh.h2_dim,
    })
}

pub(crate) fn lift_mat_z_to_q(mat: &[Vec<BigInt>]) -> Vec<Vec<Rat>> {
    mat.iter()
        .map(|row| row.iter().map(|v| Rat::from_int(v.clone())).collect())
        .collect()
}

pub(crate) fn lift_mat_z_to_fp(mat: &[Vec<BigInt>], p: &num_bigint::BigUint) -> Vec<Vec<FpElem>> {
    mat.iter()
        .map(|row| {
            row.iter()
                .map(|v| FpElem::from_checked_prime(v.clone(), p.clone()))
                .collect()
        })
        .collect()
}

pub(crate) fn map_diag_alg_err(err: crate::algebra::poly::AlgebraError) -> SilenceReason {
    match err {
        crate::algebra::poly::AlgebraError::UnobservedDependency { slots } => {
            SilenceReason::UnobservedDependency { slots }
        }
        other => SilenceReason::DiagnosticsStratificationOutOfScope {
            detail: other.to_string(),
        },
    }
}

fn diag_outcome(
    verdict: Verdict,
    coeff_domain: CoeffDomain,
    point_domain: PointDomain,
    applicability: Vec<ApplicabilityCheck>,
    provenance: Provenance,
    detail: DiagnosticsOutcomeDetail,
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
        diagnostics: Some(detail),
        atlas: None,
    }
}

fn diag_undetermined(
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
