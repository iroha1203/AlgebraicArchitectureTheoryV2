//! 整数環 $\mathbb{Z}$ 上の冪零商検出次数および一般係数冪零商 base change（$D_r$ 像 vs 抽象テンソル）（G-141 F8・H6）。

use crate::algebra::MonomialOrder;
use crate::algebra::artin::enumerate_monomials_up_to;
use crate::algebra::artin_quotient::LocalArtinQuotient;
use crate::algebra::cochain::{SmithFormZ, smith_normal_form_z};
use crate::algebra::poly::{AlgebraError, Monomial, Poly};
use crate::algebra::poly_expr::{ExprBindings, VarOrder};
use crate::algebra::scalar::{FpElem, Rat};
use crate::ir::artin::{ArtinTaskSpec, BaseChangeSpec};
use crate::ir::change::PointDomain;
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{ApplicabilityCheck, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_phase4::{
    ArtinCompositionResult, ArtinOutcomeDetail, NilpotentBaseChangeResult,
};
use crate::ir::term::CoeffDomain;
use crate::solver::artin::{
    OrderDetection, artin_outcome, artin_undetermined, compute_syntactic_degree_bound,
    detect_order_field, detection_nu, eliminate_stage, eliminate_stage_from, eval_base_point,
    expand_polys, map_artin_err, opt_min, unpack_detection, verify_base_point_vanishing,
};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use std::collections::BTreeMap;

const Z_TEST_RING_FAMILY: &str = "general_coeff_nilpotent_quotient";

pub(crate) fn solve_artin_z(
    spec: &ArtinTaskSpec,
    max_dim: usize,
    mut checks: Vec<ApplicabilityCheck>,
    provenance: Provenance,
) -> ShigureOutcome {
    let coeff_domain = CoeffDomain::Z;
    let point_domain = PointDomain::UniversalRing;

    let (obs_order, obs_bindings) = match ExprBindings::from_slices(&spec.obs_vars, &[], &[]) {
        Ok(p) => p,
        Err(e) => {
            return artin_undetermined(
                coeff_domain,
                point_domain,
                checks,
                provenance,
                map_artin_err(e),
            );
        }
    };
    let obs_rels = match expand_polys(&spec.obs_relations, &obs_bindings, &Poly::from_expr_z) {
        Ok(v) => v,
        Err(e) => {
            return artin_undetermined(
                coeff_domain,
                point_domain,
                checks,
                provenance,
                map_artin_err(e),
            );
        }
    };
    let base_pt = match eval_base_point(&spec.obs_vars, &spec.base_point, &Poly::from_expr_z) {
        Ok(v) => v,
        Err(e) => {
            return artin_undetermined(
                coeff_domain,
                point_domain,
                checks,
                provenance,
                map_artin_err(e),
            );
        }
    };

    let (stage1_subst, eliminated1) = match eliminate_stage(
        &spec.obs_vars,
        &[],
        &spec.aux_defs,
        &spec.extra_laws,
        BigInt::zero(),
        &Poly::from_expr_z,
    ) {
        Ok(p) => p,
        Err(e) => {
            return artin_undetermined(
                coeff_domain,
                point_domain,
                checks,
                provenance,
                map_artin_err(e),
            );
        }
    };

    if let Err(reason) = verify_base_point_vanishing(
        &obs_rels,
        &eliminated1,
        &base_pt,
        &spec.obs_relations,
        &spec.extra_laws,
    ) {
        checks.push(ApplicabilityCheck::failed(
            "base_point_lies_in_Sem_P",
            MathClause::G141F8,
            reason.code(),
        ));
        return artin_undetermined(coeff_domain, point_domain, checks, provenance, reason);
    }
    checks.push(ApplicabilityCheck::passed(
        "base_point_lies_in_Sem_P",
        MathClause::G141F8,
    ));

    let is_free = spec.obs_relations.is_empty();
    let syntactic_degree_bound = if is_free {
        Some(compute_syntactic_degree_bound(
            &spec.obs_vars,
            &spec.aux_defs,
            &spec.extra_laws,
        ))
    } else {
        None
    };

    let det1 = match detect_order_z(
        &obs_order,
        &obs_rels,
        &eliminated1,
        &base_pt,
        spec.max_order,
        max_dim,
    ) {
        Ok(d) => d,
        Err(reason) => {
            checks.push(ApplicabilityCheck::failed(
                "artin_order_within_bound",
                MathClause::G141F8,
                reason.code(),
            ));
            return artin_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };
    checks.push(ApplicabilityCheck::passed(
        "artin_order_within_bound",
        MathClause::G141F8,
    ));

    let (
        detection_order_nu,
        local_isomorphism_at_base,
        lift_failure_mode,
        universal_first_obstruction,
    ) = unpack_detection(det1);

    let composition_law = if let Some(stage2) = &spec.composite_stage {
        let (_, eliminated2) = match eliminate_stage_from(
            &stage1_subst,
            &stage2.aux_defs,
            &stage2.extra_laws,
            &Poly::from_expr_z,
        ) {
            Ok(p) => p,
            Err(e) => {
                return artin_undetermined(
                    coeff_domain,
                    point_domain,
                    checks,
                    provenance,
                    map_artin_err(e),
                );
            }
        };
        if let Err(reason) =
            verify_base_point_vanishing(&[], &eliminated2, &base_pt, &[], &stage2.extra_laws)
        {
            return artin_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
        let mut a1_rels = obs_rels.clone();
        a1_rels.extend(eliminated1.iter().cloned());
        let det_v = match detect_order_z(
            &obs_order,
            &a1_rels,
            &eliminated2,
            &base_pt,
            spec.max_order,
            max_dim,
        ) {
            Ok(d) => d,
            Err(reason) => {
                return artin_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        };
        let mut combined = eliminated1.clone();
        combined.extend(eliminated2);
        let det_vu = match detect_order_z(
            &obs_order,
            &obs_rels,
            &combined,
            &base_pt,
            spec.max_order,
            max_dim,
        ) {
            Ok(d) => d,
            Err(reason) => {
                return artin_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        };
        let nu_u = detection_order_nu;
        let nu_v = detection_nu(&det_v);
        let nu_vu = detection_nu(&det_vu);
        Some(ArtinCompositionResult {
            nu_u,
            nu_v,
            nu_vu,
            min_law_verified: nu_vu == opt_min(nu_u, nu_v),
        })
    } else {
        None
    };

    let base_change = if let Some(bc) = &spec.base_change {
        match compute_base_change_from_z(
            spec,
            bc,
            &obs_order,
            &obs_rels,
            &eliminated1,
            &base_pt,
            detection_order_nu,
            max_dim,
        ) {
            Ok(r) => Some(r),
            Err(reason) => {
                return artin_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        }
    } else {
        None
    };

    let eliminated_residuals = eliminated1
        .iter()
        .map(|p| p.display(&obs_order, MonomialOrder::Grevlex))
        .collect();
    let verdict = if local_isomorphism_at_base {
        Verdict::Established
    } else {
        Verdict::Refuted
    };

    let detail = ArtinOutcomeDetail {
        test_ring_family: Z_TEST_RING_FAMILY.to_owned(),
        is_free_observation_chart: is_free,
        eliminated_residuals,
        syntactic_degree_bound,
        detection_order_nu,
        local_isomorphism_at_base,
        lift_failure_mode,
        universal_first_obstruction,
        composition_law,
        base_change,
    };
    artin_outcome(verdict, coeff_domain, point_domain, checks, provenance, detail)
}

fn detect_order_z(
    obs_order: &VarOrder,
    obs_rels: &[Poly<BigInt>],
    extra_res: &[Poly<BigInt>],
    base_pt: &[BigInt],
    max_order: usize,
    max_dim: usize,
) -> Result<OrderDetection, SilenceReason> {
    if extra_res.iter().all(Poly::is_zero) {
        return Ok(OrderDetection::Infinite);
    }
    let d = obs_order.len();
    let shifted_rels: Vec<Poly<BigInt>> = obs_rels
        .iter()
        .map(|p| shift_poly_to_base(p, base_pt))
        .collect::<Result<_, _>>()
        .map_err(map_artin_err)?;
    let shifted_extra: Vec<Poly<BigInt>> = extra_res
        .iter()
        .map(|p| shift_poly_to_base(p, base_pt))
        .collect::<Result<_, _>>()
        .map_err(map_artin_err)?;

    let mut prev_dim = 1usize;
    for r in 1..=max_order {
        let monos = enumerate_monomials_up_to(d, r, max_dim).map_err(|e| {
            SilenceReason::ArtinOrderOutOfScope {
                detail: e.to_string(),
            }
        })?;
        let mono_idx: BTreeMap<Monomial, usize> = monos
            .iter()
            .enumerate()
            .map(|(i, m)| (m.clone(), i))
            .collect();
        let mut nonzero_imgs = Vec::new();
        if shifted_rels.is_empty() {
            for g in &shifted_extra {
                let trunc = g.truncate_degree(r as u64);
                if !trunc.is_zero() {
                    nonzero_imgs.push(trunc.display(obs_order, MonomialOrder::Grevlex));
                }
            }
            if !nonzero_imgs.is_empty() {
                let kernel_dim = monos.len().saturating_sub(prev_dim);
                return Ok(OrderDetection::Finite {
                    nu: r,
                    r_base_label: if r == 1 {
                        "Z".to_owned()
                    } else {
                        format!("Z[O]/m^{r}")
                    },
                    r_prime_label: format!("Z[O]/m^{}", r + 1),
                    kernel_dim,
                    kappa_u_images: nonzero_imgs,
                });
            }
            prev_dim = monos.len();
        } else {
            let cols = build_z_ideal_matrix(&shifted_rels, &monos, &mono_idx, r)
                .map_err(map_artin_err)?;
            let mat = cols_to_mat(&cols, monos.len());
            let snf = smith_normal_form_z(&mat, cols.len()).map_err(map_artin_err)?;
            for g in &shifted_extra {
                let trunc = g.truncate_degree(r as u64);
                let vec = poly_to_z_vec(&trunc, &mono_idx, monos.len());
                if !in_z_snf_image(&snf, &vec) {
                    nonzero_imgs.push(trunc.display(obs_order, MonomialOrder::Grevlex));
                }
            }
            if !nonzero_imgs.is_empty() {
                let cur_rank = monos.len().saturating_sub(snf.rank);
                let kernel_dim = cur_rank.saturating_sub(prev_dim);
                return Ok(OrderDetection::Finite {
                    nu: r,
                    r_base_label: if r == 1 {
                        "Z".to_owned()
                    } else {
                        format!("A_Z/m^{r}")
                    },
                    r_prime_label: format!("A_Z/m^{}", r + 1),
                    kernel_dim,
                    kappa_u_images: nonzero_imgs,
                });
            }
            prev_dim = monos.len().saturating_sub(snf.rank);
        }
    }

    if !shifted_rels.is_empty()
        && shifted_extra
            .iter()
            .all(|g| is_certified_in_z_ideal(g, &shifted_rels, max_dim))
    {
        return Ok(OrderDetection::Infinite);
    }

    Err(SilenceReason::ArtinOrderOutOfScope {
        detail: format!(
            "Z residuals vanished through nilpotent order {max_order} without proving J_u = 0; increase max_order"
        ),
    })
}

/// 次数有界な Z-線形結合による `g ∈ <rels>` の健全な十分証明（独立再検算付き）。
fn is_certified_in_z_ideal(g: &Poly<BigInt>, rels: &[Poly<BigInt>], max_dim: usize) -> bool {
    if g.is_zero() {
        return true;
    }
    let d = g.num_vars();
    let deg_g = usize::try_from(g.total_degree()).unwrap_or(usize::MAX);
    let Ok(target_monos) = enumerate_monomials_up_to(d, deg_g, max_dim) else {
        return false;
    };
    let mono_idx: BTreeMap<Monomial, usize> = target_monos
        .iter()
        .enumerate()
        .map(|(i, m)| (m.clone(), i))
        .collect();
    let mut cols = Vec::new();
    for h in rels {
        if h.is_zero() {
            continue;
        }
        let deg_h = usize::try_from(h.total_degree()).unwrap_or(usize::MAX);
        if deg_h > deg_g {
            continue;
        }
        let Ok(mul_monos) = enumerate_monomials_up_to(d, deg_g - deg_h, max_dim) else {
            return false;
        };
        for m in mul_monos {
            let mut mp = Poly::zero(d, BigInt::zero());
            mp.add_term(m, BigInt::one());
            let Ok(prod) = mp.checked_mul(h) else {
                return false;
            };
            if prod.total_degree() <= g.total_degree() && !prod.is_zero() {
                cols.push(poly_to_z_vec(&prod, &mono_idx, target_monos.len()));
            }
        }
    }
    if cols.is_empty() {
        return false;
    }
    let mat = cols_to_mat(&cols, target_monos.len());
    let Ok(snf) = smith_normal_form_z(&mat, cols.len()) else {
        return false;
    };
    in_z_snf_image(&snf, &poly_to_z_vec(g, &mono_idx, target_monos.len()))
}

#[allow(clippy::too_many_arguments)]
fn compute_base_change_from_z(
    spec: &ArtinTaskSpec,
    bc: &BaseChangeSpec,
    obs_order: &VarOrder,
    obs_rels: &[Poly<BigInt>],
    eliminated: &[Poly<BigInt>],
    base_pt: &[BigInt],
    source_nu: Option<usize>,
    max_dim: usize,
) -> Result<NilpotentBaseChangeResult, SilenceReason> {
    let r = bc.test_order.or(source_nu).unwrap_or(1);
    let d = obs_order.len();
    let monos = enumerate_monomials_up_to(d, r, max_dim).map_err(|e| {
        SilenceReason::ArtinOrderOutOfScope {
            detail: e.to_string(),
        }
    })?;
    let mono_idx: BTreeMap<Monomial, usize> = monos
        .iter()
        .enumerate()
        .map(|(i, m)| (m.clone(), i))
        .collect();

    let shifted_rels: Vec<Poly<BigInt>> = obs_rels
        .iter()
        .map(|p| shift_poly_to_base(p, base_pt))
        .collect::<Result<_, _>>()
        .map_err(map_artin_err)?;
    let shifted_extra: Vec<Poly<BigInt>> = eliminated
        .iter()
        .map(|p| shift_poly_to_base(p, base_pt))
        .collect::<Result<_, _>>()
        .map_err(map_artin_err)?;

    let j_cols = build_z_ideal_matrix(&shifted_extra, &monos, &mono_idx, r)
        .map_err(map_artin_err)?;
    let (dr_free_rank, dr_torsions, snf_io_opt) = if shifted_rels.is_empty() {
        let mat = cols_to_mat(&j_cols, monos.len());
        let snf = smith_normal_form_z(&mat, j_cols.len()).map_err(map_artin_err)?;
        (snf.rank, Vec::new(), None)
    } else {
        let io_cols = build_z_ideal_matrix(&shifted_rels, &monos, &mono_idx, r)
            .map_err(map_artin_err)?;
        let mut combined_cols = io_cols.clone();
        combined_cols.extend(j_cols.iter().cloned());
        let snf_io = smith_normal_form_z(&cols_to_mat(&io_cols, monos.len()), io_cols.len())
            .map_err(map_artin_err)?;
        let snf_comb = smith_normal_form_z(
            &cols_to_mat(&combined_cols, monos.len()),
            combined_cols.len(),
        )
        .map_err(map_artin_err)?;
        let (free_rank, torsions) = exact_sublattice_quotient_z(&snf_comb, &io_cols)?;
        (free_rank, torsions, Some(snf_io))
    };

    let source_dr_generators: Vec<String> = shifted_extra
        .iter()
        .map(|g| g.truncate_degree(r as u64))
        .filter(|g| {
            if g.is_zero() {
                return false;
            }
            match &snf_io_opt {
                Some(snf_io) => !in_z_snf_image(snf_io, &poly_to_z_vec(g, &mono_idx, monos.len())),
                None => true,
            }
        })
        .map(|g| g.display(obs_order, MonomialOrder::Grevlex))
        .collect();

    match &bc.target_domain {
        CoeffDomain::Z => {
            let dr_nonzero = dr_free_rank > 0 || !dr_torsions.is_empty();
            Ok(NilpotentBaseChangeResult {
                source_domain: "Z".to_owned(),
                target_domain: "Z".to_owned(),
                source_nu,
                target_nu: source_nu,
                test_order: r,
                source_dr_generators: source_dr_generators.clone(),
                abstract_tensor_nonzero: dr_nonzero,
                target_image_generators: source_dr_generators,
                target_image_is_zero: !dr_nonzero,
                flat_base_change: true,
                faithfully_flat: true,
            })
        }
        CoeffDomain::Q => {
            let obs_rels_q: Vec<Poly<Rat>> = obs_rels.iter().map(poly_z_to_q).collect();
            let extra_q: Vec<Poly<Rat>> = eliminated.iter().map(poly_z_to_q).collect();
            let base_q: Vec<Rat> = base_pt.iter().map(|v| Rat::from_int(v.clone())).collect();
            let det_q = detect_order_field(
                obs_order,
                &obs_rels_q,
                &extra_q,
                &base_q,
                spec.max_order,
                max_dim,
                Rat::zero(),
            )?;
            let target_nu = detection_nu(&det_q);
            let q_r = LocalArtinQuotient::build(
                obs_order.clone(),
                &obs_rels_q,
                &base_q,
                r,
                Rat::zero(),
                max_dim,
            )
            .map_err(|e| SilenceReason::ArtinOrderOutOfScope {
                detail: e.to_string(),
            })?;
            let mut target_imgs = Vec::new();
            for g in &extra_q {
                let v = q_r.project_poly(g).map_err(map_artin_err)?;
                if !q_r.algebra.is_zero_elem(&v) {
                    target_imgs.push(q_r.algebra.format_elem(&v));
                }
            }
            Ok(NilpotentBaseChangeResult {
                source_domain: "Z".to_owned(),
                target_domain: "Q".to_owned(),
                source_nu,
                target_nu,
                test_order: r,
                source_dr_generators,
                abstract_tensor_nonzero: dr_free_rank > 0,
                target_image_is_zero: target_imgs.is_empty(),
                target_image_generators: target_imgs,
                flat_base_change: true,
                faithfully_flat: false,
            })
        }
        CoeffDomain::Fp(p) => {
            let zero_fp = FpElem::zero(p.clone()).ok_or_else(|| {
                SilenceReason::UnsupportedCoeffRing {
                    domain: bc.target_domain.clone(),
                    detail: format!("modulus {p} is not prime"),
                }
            })?;
            let obs_rels_fp: Vec<Poly<FpElem>> =
                obs_rels.iter().map(|poly| poly_z_to_fp(poly, p)).collect();
            let extra_fp: Vec<Poly<FpElem>> =
                eliminated.iter().map(|poly| poly_z_to_fp(poly, p)).collect();
            let base_fp: Vec<FpElem> = base_pt
                .iter()
                .map(|v| FpElem::from_checked_prime(v.clone(), p.clone()))
                .collect();
            let det_fp = detect_order_field(
                obs_order,
                &obs_rels_fp,
                &extra_fp,
                &base_fp,
                spec.max_order,
                max_dim,
                zero_fp.clone(),
            )?;
            let target_nu = detection_nu(&det_fp);
            let q_r = LocalArtinQuotient::build(
                obs_order.clone(),
                &obs_rels_fp,
                &base_fp,
                r,
                zero_fp,
                max_dim,
            )
            .map_err(|e| SilenceReason::ArtinOrderOutOfScope {
                detail: e.to_string(),
            })?;
            let mut target_imgs = Vec::new();
            for g in &extra_fp {
                let v = q_r.project_poly(g).map_err(map_artin_err)?;
                if !q_r.algebra.is_zero_elem(&v) {
                    target_imgs.push(q_r.algebra.format_elem(&v));
                }
            }
            let p_int = BigInt::from(p.clone());
            let abstract_tensor_nonzero =
                dr_free_rank > 0 || dr_torsions.iter().any(|d| (d % &p_int).is_zero());
            Ok(NilpotentBaseChangeResult {
                source_domain: "Z".to_owned(),
                target_domain: format!("F_{p}"),
                source_nu,
                target_nu,
                test_order: r,
                source_dr_generators,
                abstract_tensor_nonzero,
                target_image_is_zero: target_imgs.is_empty(),
                target_image_generators: target_imgs,
                flat_base_change: false,
                faithfully_flat: false,
            })
        }
    }
}

fn shift_poly_to_base(poly: &Poly<BigInt>, base_pt: &[BigInt]) -> Result<Poly<BigInt>, AlgebraError> {
    let d = base_pt.len();
    let shift: Vec<Poly<BigInt>> = base_pt
        .iter()
        .enumerate()
        .map(|(i, a)| Poly::var(d, i, BigInt::zero()).add(&Poly::constant(d, a.clone())))
        .collect();
    poly.substitute(&shift)
}

fn poly_to_z_vec(
    poly: &Poly<BigInt>,
    mono_idx: &BTreeMap<Monomial, usize>,
    dim: usize,
) -> Vec<BigInt> {
    let mut v = vec![BigInt::zero(); dim];
    for (m, c) in poly.terms() {
        if let Some(&idx) = mono_idx.get(m) {
            v[idx] = c.clone();
        }
    }
    v
}

fn build_z_ideal_matrix(
    gens: &[Poly<BigInt>],
    monos: &[Monomial],
    mono_idx: &BTreeMap<Monomial, usize>,
    max_deg: usize,
) -> Result<Vec<Vec<BigInt>>, AlgebraError> {
    let dim = monos.len();
    let mut cols = Vec::new();
    for g in gens {
        let g_trunc = g.truncate_degree(max_deg as u64);
        if g_trunc.is_zero() {
            continue;
        }
        for m in monos {
            let mut m_poly = Poly::zero(m.num_vars(), BigInt::zero());
            m_poly.add_term(m.clone(), BigInt::one());
            let prod = m_poly.checked_mul(&g_trunc)?.truncate_degree(max_deg as u64);
            if !prod.is_zero() {
                cols.push(poly_to_z_vec(&prod, mono_idx, dim));
            }
        }
    }
    Ok(cols)
}

fn cols_to_mat(cols: &[Vec<BigInt>], num_rows: usize) -> Vec<Vec<BigInt>> {
    let num_cols = cols.len();
    let mut mat = vec![vec![BigInt::zero(); num_cols]; num_rows];
    for (c_idx, col) in cols.iter().enumerate() {
        for (row, val) in col.iter().enumerate() {
            mat[row][c_idx] = val.clone();
        }
    }
    mat
}

fn in_z_snf_image(snf: &SmithFormZ, vec: &[BigInt]) -> bool {
    let num_rows = snf.u.len();
    let mut u_vec = vec![BigInt::zero(); num_rows];
    for (i, row) in snf.u.iter().enumerate() {
        let mut acc = BigInt::zero();
        for (a, b) in row.iter().zip(vec) {
            if !a.is_zero() && !b.is_zero() {
                acc += a * b;
            }
        }
        u_vec[i] = acc;
    }
    if u_vec[snf.rank..].iter().any(|v| !v.is_zero()) {
        return false;
    }
    for (i, diag) in snf.diagonals.iter().enumerate() {
        if !(&u_vec[i] % diag).is_zero() {
            return false;
        }
    }
    true
}

/// 部分格子 `im(io_cols) ⊆ im(comb)` の商アーベル群 `im(comb) / im(io_cols)` の
/// 厳密な `(free_rank, torsion_orders)` を計算する。
fn exact_sublattice_quotient_z(
    snf_comb: &SmithFormZ,
    io_cols: &[Vec<BigInt>],
) -> Result<(usize, Vec<BigInt>), SilenceReason> {
    let r_c = snf_comb.rank;
    if r_c == 0 {
        return Ok((0, Vec::new()));
    }
    if io_cols.is_empty() {
        return Ok((r_c, Vec::new()));
    }
    let mut b_mat = vec![vec![BigInt::zero(); io_cols.len()]; r_c];
    for (c_idx, col) in io_cols.iter().enumerate() {
        for (i, diag) in snf_comb.diagonals.iter().enumerate().take(r_c) {
            let mut acc = BigInt::zero();
            for (u_ij, v_j) in snf_comb.u[i].iter().zip(col) {
                if !u_ij.is_zero() && !v_j.is_zero() {
                    acc += u_ij * v_j;
                }
            }
            if !(&acc % diag).is_zero() {
                return Err(SilenceReason::ArtinOrderOutOfScope {
                    detail: "internal Z sublattice quotient divisibility invariant violated"
                        .to_owned(),
                });
            }
            b_mat[i][c_idx] = acc / diag;
        }
    }
    let snf_rel = smith_normal_form_z(&b_mat, io_cols.len()).map_err(map_artin_err)?;
    let free_rank = r_c.saturating_sub(snf_rel.rank);
    let torsions: Vec<BigInt> = snf_rel
        .diagonals
        .into_iter()
        .filter(|d| *d > BigInt::one())
        .collect();
    Ok((free_rank, torsions))
}

fn poly_z_to_q(poly: &Poly<BigInt>) -> Poly<Rat> {
    let mut out = Poly::zero(poly.num_vars(), Rat::zero());
    for (m, c) in poly.terms() {
        out.add_term(m.clone(), Rat::from_int(c.clone()));
    }
    out
}

fn poly_z_to_fp(poly: &Poly<BigInt>, p: &BigUint) -> Poly<FpElem> {
    let zero = FpElem::from_checked_prime(BigInt::zero(), p.clone());
    let mut out = Poly::zero(poly.num_vars(), zero);
    for (m, c) in poly.terms() {
        out.add_term(m.clone(), FpElem::from_checked_prime(c.clone(), p.clone()));
    }
    out
}
