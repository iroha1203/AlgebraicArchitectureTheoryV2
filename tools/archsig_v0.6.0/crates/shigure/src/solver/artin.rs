//! 定義的補助演算の原始消去（F1）・全局所 Artin 試験（F2–F3）・普遍初回障害 $\kappa_u$（F4–F5）・
//! 2 段合成則（F6）・自由観測 chart 構文次数上界 $D$（F7）・非 Noetherian 沈黙（H7）の計算核。

use crate::algebra::MonomialOrder;
use crate::algebra::artin::DEFAULT_MAX_ARTIN_DIM;
use crate::algebra::artin_quotient::LocalArtinQuotient;
use crate::algebra::poly::{AlgebraError, Poly};
use crate::algebra::poly_expr::{ExprBindings, VarOrder};
use crate::algebra::scalar::{FpElem, Rat, RingCoeff};
use crate::algebra::syzygy::{
    DEFAULT_MAX_SYZYGY_PAIRS, FieldCoeff, compute_syzygies_field, ideal_membership_field,
};
use crate::ir::artin::{ArtinTaskSpec, AuxiliaryDefSpec, BaseChangeSpec, CheckedArtinTask};
use crate::ir::change::{NamedPoly, PointDomain};
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{ApplicabilityCheck, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_phase4::{
    ArtinCompositionResult, ArtinOutcomeDetail, NilpotentBaseChangeResult,
    UniversalObstructionSummary,
};
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::solver::artin_z::solve_artin_z;
use crate::solver::lift_common::eval_const_expr;
use std::collections::{BTreeMap, BTreeSet};

pub(crate) const TEST_RING_FAMILY: &str = "all_local_artin_algebras_universal_quotient";

/// `shigure_artin` の計算核入口（G-141 F1–F9・H4–H7・H10）。
pub fn solve_artin_task(task: &CheckedArtinTask) -> ShigureOutcome {
    let spec = task.spec();
    let coeff_domain = spec.coeff_domain.clone();
    let point_domain = PointDomain::UniversalRing;
    let provenance = build_artin_provenance(spec);
    let mut checks = Vec::new();

    // H7: 非 Noetherian 無限表示は全 Artin 試験一致から局所同型を主張できず即座に沈黙する（G-141 F3・H7）。
    if spec.non_noetherian_infinite {
        let reason = SilenceReason::NonNoetherianInfinitePresentation {
            detail: "presentation is marked non-Noetherian / infinite; Krull intersection theorem does not apply, so agreement on all local Artin tests does not imply local isomorphism".to_owned(),
        };
        checks.push(ApplicabilityCheck::failed(
            "noetherian_finite_presentation",
            MathClause::G141F3,
            "non_noetherian_infinite flag is true",
        ));
        return artin_undetermined(coeff_domain, point_domain, checks, provenance, reason);
    }
    checks.push(ApplicabilityCheck::passed(
        "noetherian_finite_presentation",
        MathClause::G141F3,
    ));

    let missing = collect_artin_unobserved(spec);
    if !missing.is_empty() {
        checks.push(ApplicabilityCheck::failed(
            "unobserved_slots_absent",
            MathClause::G140P0Dot1,
            format!("missing slots: {}", missing.join(", ")),
        ));
        return artin_undetermined(
            coeff_domain,
            point_domain,
            checks,
            provenance,
            SilenceReason::UnobservedDependency { slots: missing },
        );
    }
    checks.push(ApplicabilityCheck::passed(
        "unobserved_slots_absent",
        MathClause::G140P0Dot1,
    ));

    let max_dim = spec.max_artin_dim.unwrap_or(DEFAULT_MAX_ARTIN_DIM);
    match &spec.coeff_domain {
        CoeffDomain::Q => solve_artin_field(
            spec,
            Rat::zero(),
            max_dim,
            &|e, b| Poly::from_expr_q(e, b),
            checks,
            provenance,
        ),
        CoeffDomain::Fp(p) => {
            let Some(zero_fp) = FpElem::zero(p.clone()) else {
                return artin_undetermined(
                    coeff_domain.clone(),
                    point_domain,
                    checks,
                    provenance,
                    SilenceReason::UnsupportedCoeffRing {
                        domain: coeff_domain,
                        detail: format!("modulus {p} is not prime"),
                    },
                );
            };
            let p_clone = p.clone();
            solve_artin_field(
                spec,
                zero_fp,
                max_dim,
                &move |e, b| Poly::from_expr_fp(e, b, &p_clone),
                checks,
                provenance,
            )
        }
        CoeffDomain::Z => solve_artin_z(spec, max_dim, checks, provenance),
    }
}

pub(crate) enum OrderDetection {
    Finite {
        nu: usize,
        r_base_label: String,
        r_prime_label: String,
        kernel_dim: usize,
        kappa_u_images: Vec<String>,
        two_context_cech_matches: bool,
    },
    Infinite,
}

fn solve_artin_field<C, FE>(
    spec: &ArtinTaskSpec,
    zero_coeff: C,
    max_dim: usize,
    expand_expr: &FE,
    mut checks: Vec<ApplicabilityCheck>,
    provenance: Provenance,
) -> ShigureOutcome
where
    C: FieldCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
{
    let coeff_domain = spec.coeff_domain.clone();
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

    let obs_rels = match expand_polys(&spec.obs_relations, &obs_bindings, expand_expr) {
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

    let base_pt = match eval_base_point(&spec.obs_vars, &spec.base_point, expand_expr) {
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
        zero_coeff.clone(),
        expand_expr,
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
            MathClause::G141F2,
            reason.code(),
        ));
        return artin_undetermined(coeff_domain, point_domain, checks, provenance, reason);
    }
    checks.push(ApplicabilityCheck::passed(
        "base_point_lies_in_Sem_P",
        MathClause::G141F2,
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

    let det1 = match detect_order_field(
        &obs_order,
        &obs_rels,
        &eliminated1,
        &base_pt,
        spec.max_order,
        max_dim,
        zero_coeff.clone(),
    ) {
        Ok(d) => d,
        Err(reason) => {
            checks.push(ApplicabilityCheck::failed(
                "artin_order_within_bound",
                MathClause::G141F2,
                reason.code(),
            ));
            return artin_undetermined(coeff_domain, point_domain, checks, provenance, reason);
        }
    };
    checks.push(ApplicabilityCheck::passed(
        "artin_order_within_bound",
        MathClause::G141F2,
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
            expand_expr,
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
        let det_v = match detect_order_field(
            &obs_order,
            &a1_rels,
            &eliminated2,
            &base_pt,
            spec.max_order,
            max_dim,
            zero_coeff.clone(),
        ) {
            Ok(d) => d,
            Err(reason) => {
                return artin_undetermined(coeff_domain, point_domain, checks, provenance, reason);
            }
        };
        let mut combined_extra = eliminated1.clone();
        combined_extra.extend(eliminated2);
        let det_vu = match detect_order_field(
            &obs_order,
            &obs_rels,
            &combined_extra,
            &base_pt,
            spec.max_order,
            max_dim,
            zero_coeff.clone(),
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
        match compute_base_change_from_field(
            spec,
            bc,
            &obs_order,
            &obs_rels,
            &eliminated1,
            &base_pt,
            detection_order_nu,
            max_dim,
            zero_coeff,
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
        test_ring_family: TEST_RING_FAMILY.to_owned(),
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
    artin_outcome(
        verdict,
        coeff_domain,
        point_domain,
        checks,
        provenance,
        detail,
    )
}

/// F2–F3: 体上の普遍局所 Artin 商 `A / m^{r+1}` で初回検出次数 `ν` を決定する。
pub(crate) fn detect_order_field<C: FieldCoeff>(
    obs_order: &VarOrder,
    obs_rels: &[Poly<C>],
    extra_res: &[Poly<C>],
    base_pt: &[C],
    max_order: usize,
    max_dim: usize,
    zero_coeff: C,
) -> Result<OrderDetection, SilenceReason> {
    if extra_res.iter().all(Poly::is_zero) {
        return Ok(OrderDetection::Infinite);
    }

    let mut prev_dim = 1usize;
    let mut prev_label = "A/m".to_owned();
    let mut stabilized = false;

    for r in 1..=max_order {
        let q_r = LocalArtinQuotient::build(
            obs_order.clone(),
            obs_rels,
            base_pt,
            r,
            zero_coeff.clone(),
            max_dim,
        )
        .map_err(|e| SilenceReason::ArtinOrderOutOfScope {
            detail: e.to_string(),
        })?;
        let mut nonzero_imgs = Vec::new();
        let mut projected_tuple = Vec::with_capacity(extra_res.len());
        for g in extra_res {
            let proj = q_r.project_poly(g).map_err(map_artin_err)?;
            if !q_r.algebra.is_zero_elem(&proj) {
                nonzero_imgs.push(q_r.algebra.format_elem(&proj));
            }
            projected_tuple.push(proj);
        }
        if !nonzero_imgs.is_empty() {
            let r_prime_label = format!("A/m^{}", r + 1);
            let kernel_dim = q_r.algebra.dim().saturating_sub(prev_dim);
            // F5 検証: [extra_res..., obs_rels...] の全 syzygy から A = K[O]/I_O 上の
            // 全 syzygy（先頭 extra_res.len() 成分）を抽出し、基点評価線形関係
            // sum_α s_α(base_pt) * bar_G_α = 0 in A/m^{ν+1} を実計算で検算する。
            let mut all_gens = Vec::with_capacity(extra_res.len() + obs_rels.len());
            all_gens.extend_from_slice(extra_res);
            all_gens.extend_from_slice(obs_rels);
            let syz = compute_syzygies_field(
                &all_gens,
                obs_order.clone(),
                MonomialOrder::Grevlex,
                DEFAULT_MAX_SYZYGY_PAIRS,
            )
            .map_err(|e| SilenceReason::SyzygyOutOfScope {
                detail: e.to_string(),
            })?;
            let two_context_cech_matches = syz.generators.iter().all(|s_vec| {
                let mut acc = q_r.algebra.zero_elem();
                for (s_poly, img) in s_vec.iter().take(extra_res.len()).zip(&projected_tuple) {
                    let Ok(c) = s_poly.eval_at(base_pt) else {
                        return false;
                    };
                    if !c.coeff_is_zero() {
                        let scaled = q_r.algebra.scale(img, &c);
                        acc = q_r.algebra.add(&acc, &scaled);
                    }
                }
                q_r.algebra.is_zero_elem(&acc)
            });
            return Ok(OrderDetection::Finite {
                nu: r,
                r_base_label: prev_label,
                r_prime_label,
                kernel_dim,
                kappa_u_images: nonzero_imgs,
                two_context_cech_matches,
            });
        }
        if q_r.algebra.dim() == prev_dim {
            stabilized = true;
            break;
        }
        prev_dim = q_r.algebra.dim();
        prev_label = format!("A/m^{}", r + 1);
    }

    if stabilized {
        return Ok(OrderDetection::Infinite);
    }
    if !obs_rels.is_empty() {
        let mut all_in_ideal = true;
        for g in extra_res {
            match ideal_membership_field(
                g,
                obs_rels,
                obs_order,
                MonomialOrder::Grevlex,
                DEFAULT_MAX_SYZYGY_PAIRS,
            ) {
                Ok(Some(_)) => {}
                Ok(None) => {
                    all_in_ideal = false;
                    break;
                }
                Err(e) => return Err(map_artin_err(e)),
            }
        }
        if all_in_ideal {
            return Ok(OrderDetection::Infinite);
        }
    }
    Err(SilenceReason::ArtinOrderOutOfScope {
        detail: format!(
            "residuals vanished through Artin order {max_order} without certifying local isomorphism; increase max_order"
        ),
    })
}

#[allow(clippy::too_many_arguments)]
fn compute_base_change_from_field<C: FieldCoeff>(
    spec: &ArtinTaskSpec,
    bc: &BaseChangeSpec,
    obs_order: &VarOrder,
    obs_rels: &[Poly<C>],
    eliminated: &[Poly<C>],
    base_pt: &[C],
    source_nu: Option<usize>,
    max_dim: usize,
    zero: C,
) -> Result<NilpotentBaseChangeResult, SilenceReason> {
    if bc.target_domain != spec.coeff_domain {
        return Err(SilenceReason::UnsupportedCoeffRing {
            domain: bc.target_domain.clone(),
            detail: format!(
                "no canonical ring homomorphism from {} to {}",
                spec.coeff_domain, bc.target_domain
            ),
        });
    }
    let r = bc.test_order.or(source_nu).unwrap_or(1);
    let q_r = LocalArtinQuotient::build(obs_order.clone(), obs_rels, base_pt, r, zero, max_dim)
        .map_err(|e| SilenceReason::ArtinOrderOutOfScope {
            detail: e.to_string(),
        })?;
    let mut imgs = Vec::new();
    for g in eliminated {
        let v = q_r.project_poly(g).map_err(map_artin_err)?;
        if !q_r.algebra.is_zero_elem(&v) {
            imgs.push(q_r.algebra.format_elem(&v));
        }
    }
    let dom_str = spec.coeff_domain.to_string();
    Ok(NilpotentBaseChangeResult {
        source_domain: dom_str.clone(),
        target_domain: dom_str,
        source_nu,
        target_nu: source_nu,
        test_order: r,
        source_dr_generators: imgs.clone(),
        abstract_tensor_nonzero: !imgs.is_empty(),
        target_image_is_zero: imgs.is_empty(),
        target_image_generators: imgs,
        flat_base_change: true,
        faithfully_flat: true,
    })
}

// =========================================================================
// 共通ヘルパ（artin_z からも共用）
// =========================================================================

pub(crate) type EliminatedStage<C> = (Vec<(String, Poly<C>)>, Vec<Poly<C>>);

pub(crate) fn eliminate_stage<C, FE>(
    obs_vars: &[String],
    initial_aux: &[(String, Poly<C>)],
    aux_defs: &[AuxiliaryDefSpec],
    extra_laws: &[NamedPoly],
    zero_coeff: C,
    expand_expr: &FE,
) -> Result<EliminatedStage<C>, AlgebraError>
where
    C: RingCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
{
    let n_obs = obs_vars.len();
    let mut subst: Vec<(String, Poly<C>)> = obs_vars
        .iter()
        .enumerate()
        .map(|(i, name)| (name.clone(), Poly::var(n_obs, i, zero_coeff.clone())))
        .collect();
    subst.extend_from_slice(initial_aux);
    eliminate_stage_from(&subst, aux_defs, extra_laws, expand_expr)
}

pub(crate) fn eliminate_stage_from<C, FE>(
    initial_subst: &[(String, Poly<C>)],
    aux_defs: &[AuxiliaryDefSpec],
    extra_laws: &[NamedPoly],
    expand_expr: &FE,
) -> Result<EliminatedStage<C>, AlgebraError>
where
    C: RingCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
{
    let mut subst = initial_subst.to_vec();
    for aux in aux_defs {
        let names: Vec<String> = subst.iter().map(|(n, _)| n.clone()).collect();
        let (_, bindings) = ExprBindings::from_slices(&names, &[], &[])?;
        let raw_poly = expand_expr(&aux.expr, &bindings)?;
        let values: Vec<Poly<C>> = subst.iter().map(|(_, p)| p.clone()).collect();
        subst.push((aux.name.clone(), raw_poly.substitute(&values)?));
    }
    let names: Vec<String> = subst.iter().map(|(n, _)| n.clone()).collect();
    let (_, bindings) = ExprBindings::from_slices(&names, &[], &[])?;
    let values: Vec<Poly<C>> = subst.iter().map(|(_, p)| p.clone()).collect();
    let mut eliminated = Vec::with_capacity(extra_laws.len());
    for law in extra_laws {
        let raw_poly = expand_expr(&law.expr, &bindings)?;
        eliminated.push(raw_poly.substitute(&values)?);
    }
    Ok((subst, eliminated))
}

pub(crate) fn compute_syntactic_degree_bound(
    obs_vars: &[String],
    aux_defs: &[AuxiliaryDefSpec],
    extra_laws: &[NamedPoly],
) -> u64 {
    let mut deg_map: BTreeMap<&str, u64> = obs_vars.iter().map(|v| (v.as_str(), 1u64)).collect();
    for aux in aux_defs {
        let d = syntactic_expr_deg(&aux.expr, &deg_map);
        deg_map.insert(aux.name.as_str(), d);
    }
    extra_laws
        .iter()
        .map(|law| syntactic_expr_deg(&law.expr, &deg_map))
        .max()
        .unwrap_or(0)
}

fn syntactic_expr_deg(expr: &PolyExpr, deg_map: &BTreeMap<&str, u64>) -> u64 {
    match expr {
        PolyExpr::Const(_) | PolyExpr::Unobserved { .. } => 0,
        PolyExpr::StateVar(v) | PolyExpr::ArgVar(v) | PolyExpr::ParamVar(v) => {
            deg_map.get(v.as_str()).copied().unwrap_or(1)
        }
        PolyExpr::Neg(a) => syntactic_expr_deg(a, deg_map),
        PolyExpr::Add(a, b) | PolyExpr::Sub(a, b) => {
            syntactic_expr_deg(a, deg_map).max(syntactic_expr_deg(b, deg_map))
        }
        PolyExpr::Mul(a, b) => {
            syntactic_expr_deg(a, deg_map).saturating_add(syntactic_expr_deg(b, deg_map))
        }
        PolyExpr::Pow(a, exp) => syntactic_expr_deg(a, deg_map).saturating_mul(u64::from(*exp)),
    }
}

pub(crate) fn verify_base_point_vanishing<C: RingCoeff>(
    obs_rels: &[Poly<C>],
    eliminated: &[Poly<C>],
    base_pt: &[C],
    obs_rel_specs: &[NamedPoly],
    extra_law_specs: &[NamedPoly],
) -> Result<(), SilenceReason> {
    for (idx, poly) in obs_rels.iter().enumerate() {
        let v = poly.eval_at(base_pt).map_err(map_artin_err)?;
        if !v.coeff_is_zero() {
            let name = obs_rel_specs
                .get(idx)
                .map(|r| r.name.as_str())
                .unwrap_or("obs_relation");
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "base_point_lies_in_Sem_P".to_owned(),
                detail: format!("obs_relation `{name}` evaluates to {v} != 0 at base_point"),
            });
        }
    }
    for (idx, poly) in eliminated.iter().enumerate() {
        let v = poly.eval_at(base_pt).map_err(map_artin_err)?;
        if !v.coeff_is_zero() {
            let name = extra_law_specs
                .get(idx)
                .map(|r| r.name.as_str())
                .unwrap_or("extra_law");
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "base_point_lies_in_Sem_P".to_owned(),
                detail: format!(
                    "eliminated extra_law `{name}` evaluates to {v} != 0 at base_point (not in Sem_P(k))"
                ),
            });
        }
    }
    Ok(())
}

pub(crate) fn unpack_detection(
    det: OrderDetection,
) -> (
    Option<usize>,
    bool,
    String,
    Option<UniversalObstructionSummary>,
) {
    match det {
        OrderDetection::Infinite => (None, true, "infinite_local_iso".to_owned(), None),
        OrderDetection::Finite {
            nu,
            r_base_label,
            r_prime_label,
            kernel_dim,
            kappa_u_images,
            two_context_cech_matches,
        } => {
            let constant_lift_exists = nu == 1;
            let mode = if nu == 1 {
                "nu_eq_1_designated_direction_only_constant_lift_exists".to_owned()
            } else {
                "nu_ge_2_realization_unliftable".to_owned()
            };
            let kappa_u_nonzero = !kappa_u_images.is_empty();
            (
                Some(nu),
                false,
                mode,
                Some(UniversalObstructionSummary {
                    nu,
                    r_base_label,
                    r_prime_label,
                    kernel_dim,
                    kappa_u_images,
                    kappa_u_nonzero,
                    two_context_cech_matches,
                    constant_lift_exists,
                }),
            )
        }
    }
}

pub(crate) fn detection_nu(det: &OrderDetection) -> Option<usize> {
    match det {
        OrderDetection::Finite { nu, .. } => Some(*nu),
        OrderDetection::Infinite => None,
    }
}

pub(crate) fn opt_min(a: Option<usize>, b: Option<usize>) -> Option<usize> {
    match (a, b) {
        (Some(x), Some(y)) => Some(x.min(y)),
        (Some(x), None) | (None, Some(x)) => Some(x),
        (None, None) => None,
    }
}

pub(crate) fn expand_polys<C, FE>(
    items: &[NamedPoly],
    bindings: &ExprBindings,
    expand_expr: &FE,
) -> Result<Vec<Poly<C>>, AlgebraError>
where
    C: RingCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
{
    items
        .iter()
        .map(|item| expand_expr(&item.expr, bindings))
        .collect()
}

pub(crate) fn eval_base_point<C, FE>(
    obs_vars: &[String],
    base_point: &[(String, PolyExpr)],
    expand_expr: &FE,
) -> Result<Vec<C>, AlgebraError>
where
    C: RingCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
{
    let map: BTreeMap<&str, &PolyExpr> = base_point.iter().map(|(k, v)| (k.as_str(), v)).collect();
    let mut out = Vec::with_capacity(obs_vars.len());
    for v in obs_vars {
        let e = map
            .get(v.as_str())
            .ok_or_else(|| AlgebraError::UnknownVariable { name: v.clone() })?;
        out.push(eval_const_expr(e, expand_expr)?);
    }
    Ok(out)
}

pub(crate) fn map_artin_err(err: AlgebraError) -> SilenceReason {
    match err {
        AlgebraError::UnobservedDependency { slots } => {
            SilenceReason::UnobservedDependency { slots }
        }
        AlgebraError::OutOfScope { detail } => SilenceReason::ArtinOrderOutOfScope { detail },
        other => SilenceReason::ApplicabilityConditionNotMet {
            condition: "artin_algebra_computation".to_owned(),
            detail: other.to_string(),
        },
    }
}

fn build_artin_provenance(spec: &ArtinTaskSpec) -> Provenance {
    let mut clauses = spec.provenance.clauses.clone();
    for c in [
        MathClause::G141F1,
        MathClause::G141F2,
        MathClause::G141F3,
        MathClause::G141F4,
        MathClause::G141F5,
        MathClause::G141F9,
    ] {
        if !clauses.contains(&c) {
            clauses.push(c);
        }
    }
    if spec.obs_relations.is_empty() && !clauses.contains(&MathClause::G141F7) {
        clauses.push(MathClause::G141F7);
    }
    if spec.composite_stage.is_some() && !clauses.contains(&MathClause::G141F6) {
        clauses.push(MathClause::G141F6);
    }
    if spec.base_change.is_some() && !clauses.contains(&MathClause::G141F8) {
        clauses.push(MathClause::G141F8);
    }
    Provenance::new(spec.provenance.origins.clone(), clauses)
}

fn collect_artin_unobserved(spec: &ArtinTaskSpec) -> Vec<String> {
    let mut slots = BTreeSet::new();
    for rel in &spec.obs_relations {
        rel.expr.collect_unobserved(&mut slots);
    }
    for aux in &spec.aux_defs {
        aux.expr.collect_unobserved(&mut slots);
    }
    for law in &spec.extra_laws {
        law.expr.collect_unobserved(&mut slots);
    }
    for (_, expr) in &spec.base_point {
        expr.collect_unobserved(&mut slots);
    }
    if let Some(st) = &spec.composite_stage {
        for aux in &st.aux_defs {
            aux.expr.collect_unobserved(&mut slots);
        }
        for law in &st.extra_laws {
            law.expr.collect_unobserved(&mut slots);
        }
    }
    slots.into_iter().collect()
}

pub(crate) fn artin_undetermined(
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

pub(crate) fn artin_outcome(
    verdict: Verdict,
    coeff_domain: CoeffDomain,
    point_domain: PointDomain,
    applicability: Vec<ApplicabilityCheck>,
    provenance: Provenance,
    detail: ArtinOutcomeDetail,
) -> ShigureOutcome {
    ShigureOutcome {
        verdict,
        coeff_domain,
        point_domain,
        applicability,
        provenance,
        residual_ideal: detail.eliminated_residuals.clone(),
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
        artin: Some(detail),
        diagnostics: None,
        atlas: None,
    }
}
