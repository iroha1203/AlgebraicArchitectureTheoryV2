//! 整数環 $\mathbb{Z}$ 上の冪零商検出次数および一般係数冪零商 base change（$D_r$ 像 vs 抽象テンソル）（G-141 F8・H6）。

use crate::algebra::MonomialOrder;
use crate::algebra::artin::enumerate_monomials_up_to;
use crate::algebra::artin_quotient::LocalArtinQuotient;
use crate::algebra::cochain::{SmithFormZ, smith_normal_form_z};
use crate::algebra::linear::{AffineSolutionZ, solve_affine_z};
use crate::algebra::poly::{AlgebraError, Monomial, Poly};
use crate::algebra::poly_expr::{ExprBindings, VarOrder};
use crate::algebra::scalar::{FpElem, Rat};
use crate::algebra::syzygy::compute_syzygies_z;
use crate::ir::provenance::MathClause;
use crate::ir::result::SilenceReason;
use crate::ir::result_phase4::NilpotentBaseChangeResult;
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::solver::artin::{
    ArtinBaseChangeInput, ArtinRingBackend, OrderDetection, detect_order_field, detection_nu,
    map_artin_err,
};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use std::collections::BTreeMap;

const Z_TEST_RING_FAMILY: &str = "general_coeff_nilpotent_quotient";

pub(crate) struct ZArtinBackend;

impl ArtinRingBackend for ZArtinBackend {
    type Coeff = BigInt;

    fn test_ring_family(&self) -> &'static str {
        Z_TEST_RING_FAMILY
    }

    fn check_clause(&self) -> MathClause {
        MathClause::G141F8
    }

    fn zero(&self) -> BigInt {
        BigInt::zero()
    }

    fn expand_expr(
        &self,
        expr: &PolyExpr,
        bindings: &ExprBindings,
    ) -> Result<Poly<BigInt>, AlgebraError> {
        Poly::from_expr_z(expr, bindings)
    }

    fn detect_order(
        &self,
        obs_order: &VarOrder,
        obs_rels: &[Poly<BigInt>],
        extra_res: &[Poly<BigInt>],
        base_pt: &[BigInt],
        max_order: usize,
        max_dim: usize,
    ) -> Result<OrderDetection, SilenceReason> {
        detect_order_z(obs_order, obs_rels, extra_res, base_pt, max_order, max_dim)
    }

    fn compute_base_change(
        &self,
        input: &ArtinBaseChangeInput<'_, BigInt>,
    ) -> Result<NilpotentBaseChangeResult, SilenceReason> {
        compute_base_change_from_z(input)
    }
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
            let mut trunc_vecs = Vec::with_capacity(shifted_extra.len());
            for g in &shifted_extra {
                let trunc = g.truncate_degree(r as u64);
                if !trunc.is_zero() {
                    nonzero_imgs.push(trunc.display(obs_order, MonomialOrder::Grevlex));
                }
                trunc_vecs.push(poly_to_z_vec(&trunc, &mono_idx, monos.len()));
            }
            if !nonzero_imgs.is_empty() {
                let kernel_dim = monos.len().saturating_sub(prev_dim);
                let two_context_cech_matches = verify_z_f5_syzygies(
                    extra_res,
                    obs_rels,
                    obs_order,
                    base_pt,
                    &trunc_vecs,
                    None,
                )?;
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
                    two_context_cech_matches,
                });
            }
            prev_dim = monos.len();
        } else {
            let cols =
                build_z_ideal_matrix(&shifted_rels, &monos, &mono_idx, r).map_err(map_artin_err)?;
            let mat = cols_to_mat(&cols, monos.len());
            let snf = smith_normal_form_z(&mat, cols.len()).map_err(map_artin_err)?;
            let mut trunc_vecs = Vec::with_capacity(shifted_extra.len());
            for g in &shifted_extra {
                let trunc = g.truncate_degree(r as u64);
                let vec = poly_to_z_vec(&trunc, &mono_idx, monos.len());
                if !in_z_snf_image(&snf, &vec) {
                    nonzero_imgs.push(trunc.display(obs_order, MonomialOrder::Grevlex));
                }
                trunc_vecs.push(vec);
            }
            if !nonzero_imgs.is_empty() {
                let mut comb_r = cols.clone();
                for (m_idx, m) in monos.iter().enumerate() {
                    if m.total_degree() == r as u64 {
                        let mut e = vec![BigInt::zero(); monos.len()];
                        e[m_idx] = BigInt::one();
                        comb_r.push(e);
                    }
                }
                let snf_comb_r =
                    smith_normal_form_z(&cols_to_mat(&comb_r, monos.len()), comb_r.len())
                        .map_err(map_artin_err)?;
                let (k_free, k_tors) = exact_sublattice_quotient_z(&snf_comb_r, &cols)?;
                let kernel_dim = k_free + k_tors.len();
                let two_context_cech_matches = verify_z_f5_syzygies(
                    extra_res,
                    obs_rels,
                    obs_order,
                    base_pt,
                    &trunc_vecs,
                    Some(&snf),
                )?;
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
                    two_context_cech_matches,
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

/// F5 検証: Z 上の `[extra_res..., obs_rels...]` の syzygy 関係（A_Z = Z[O]/I_O 上の syzygy）が
/// `A_Z/m^{ν+1}` 上の像タプルを零化することを検算する。未保証非線形族は fail-closed に沈黙する。
fn verify_z_f5_syzygies(
    extra_res: &[Poly<BigInt>],
    obs_rels: &[Poly<BigInt>],
    obs_order: &VarOrder,
    base_pt: &[BigInt],
    trunc_vecs: &[Vec<BigInt>],
    snf_io: Option<&SmithFormZ>,
) -> Result<bool, SilenceReason> {
    let dim = trunc_vecs.first().map_or(0, Vec::len);
    let mut all_gens = Vec::with_capacity(extra_res.len() + obs_rels.len());
    all_gens.extend_from_slice(extra_res);
    all_gens.extend_from_slice(obs_rels);
    if all_gens.len() <= 1 {
        return Ok(true);
    }
    let syz = compute_syzygies_z(&all_gens, obs_order.clone()).map_err(|e| {
        SilenceReason::SyzygyOutOfScope {
            detail: e.to_string(),
        }
    })?;
    let ok = syz.generators.iter().all(|s_vec| {
        let mut acc = vec![BigInt::zero(); dim];
        for (s_poly, img) in s_vec.iter().take(extra_res.len()).zip(trunc_vecs) {
            let Ok(c) = s_poly.eval_at(base_pt) else {
                return false;
            };
            if !c.is_zero() {
                for (dst, v) in acc.iter_mut().zip(img) {
                    *dst += &c * v;
                }
            }
        }
        match snf_io {
            Some(snf) => in_z_snf_image(snf, &acc),
            None => acc.iter().all(Zero::is_zero),
        }
    });
    Ok(ok)
}

/// 次数有界な Z-線形結合による `g ∈ <rels>` の健全な十分証明（cofactor 再構成による独立再検算付き）。
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
    let mut prod_polys = Vec::new();
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
                prod_polys.push(prod);
            }
        }
    }
    if cols.is_empty() {
        return false;
    }
    let mat = cols_to_mat(&cols, target_monos.len());
    let target_vec = poly_to_z_vec(g, &mono_idx, target_monos.len());
    let Ok(AffineSolutionZ::Consistent { particular, .. }) =
        solve_affine_z(&mat, &target_vec, cols.len())
    else {
        return false;
    };
    let mut reconstructed = Poly::zero(d, BigInt::zero());
    for (coeff, prod) in particular.iter().zip(&prod_polys) {
        if !coeff.is_zero() {
            reconstructed = reconstructed.add(&prod.scale(coeff));
        }
    }
    reconstructed == *g
}

fn compute_base_change_from_z(
    input: &ArtinBaseChangeInput<'_, BigInt>,
) -> Result<NilpotentBaseChangeResult, SilenceReason> {
    let spec = input.spec;
    let bc = input.bc;
    let obs_order = input.obs_order;
    let obs_rels = input.obs_rels;
    let eliminated = input.eliminated;
    let base_pt = input.base_pt;
    let source_nu = input.source_nu;
    let max_dim = input.max_dim;
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

    let j_cols =
        build_z_ideal_matrix(&shifted_extra, &monos, &mono_idx, r).map_err(map_artin_err)?;
    let (dr_free_rank, dr_torsions, snf_io_opt) = if shifted_rels.is_empty() {
        let mat = cols_to_mat(&j_cols, monos.len());
        let snf = smith_normal_form_z(&mat, j_cols.len()).map_err(map_artin_err)?;
        (snf.rank, Vec::new(), None)
    } else {
        let io_cols =
            build_z_ideal_matrix(&shifted_rels, &monos, &mono_idx, r).map_err(map_artin_err)?;
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
            let zero_fp =
                FpElem::zero(p.clone()).ok_or_else(|| SilenceReason::UnsupportedCoeffRing {
                    domain: bc.target_domain.clone(),
                    detail: format!("modulus {p} is not prime"),
                })?;
            let obs_rels_fp: Vec<Poly<FpElem>> =
                obs_rels.iter().map(|poly| poly_z_to_fp(poly, p)).collect();
            let extra_fp: Vec<Poly<FpElem>> = eliminated
                .iter()
                .map(|poly| poly_z_to_fp(poly, p))
                .collect();
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

fn shift_poly_to_base(
    poly: &Poly<BigInt>,
    base_pt: &[BigInt],
) -> Result<Poly<BigInt>, AlgebraError> {
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
            let prod = m_poly
                .checked_mul(&g_trunc)?
                .truncate_degree(max_deg as u64);
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
