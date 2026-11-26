//! `shigure diagnostics` 宣言および共通 K1 `SupportedNerve` の静的意味検査（Phase 4 / AC2）。

use super::ast_ext::ShigureScalarLit;
use super::ast_phase4_diag_atlas::*;
use super::check::{
    CResult, LiteralDomainRule, check_coeff_domain, check_poly_literals, check_poly_vars,
    resolve_observed_field,
};
use super::check_ext_common::check_scalar_lit;
use super::check_family::check_named_polys_in_scope;
use super::check_phase4_lift_artin::{
    check_p4_coord_scalar_map, check_p4_coord_vec_map, check_p4_origins, check_p4_unique_idents,
    p4_type_err,
};
use super::*;
use crate::law::ast::{Ident, Span};
use crate::law::check::{Checker, duplicate, full, reference};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::json::InputError;
use std::collections::{HashMap, HashSet};

/// K1 `TargetSupportedNerve` の chart・edge・face 端点等式を静的検査する（Atlas 細分化でも共用）。
pub(super) fn check_supported_nerve<E: InputError>(
    raw: &RawSupportedNerve,
    valid_targets: &HashSet<&str>,
    context: &str,
    control: &Control,
) -> CResult<ShigureSupportedNerve, E> {
    let mut chart_names = HashSet::new();
    let mut charts = Vec::with_capacity(raw.charts.len());
    for ch in &raw.charts {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !chart_names.insert(ch.name.name.as_str()) {
            return duplicate(
                ch.name.span,
                format!("duplicate nerve chart `{}` in {context}", ch.name.name),
            );
        }
        let support = check_p4_unique_idents(&ch.support, "chart support", context)?;
        for s in &support {
            if !valid_targets.contains(s.as_str()) {
                return reference(
                    ch.span,
                    format!(
                        "unknown target `{s}` in nerve chart `{}` ({context})",
                        ch.name.name
                    ),
                );
            }
        }
        charts.push(ShigureChartSupport {
            name: ch.name.name.clone(),
            support,
            span: ch.span,
        });
    }

    let mut edge_endpoints: HashMap<&str, (&str, &str)> = HashMap::new();
    let mut edges = Vec::with_capacity(raw.edges.len());
    for e in &raw.edges {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if e.name.name == "none" {
            return p4_type_err(e.name.span, "nerve edge name `none` is reserved");
        }
        if !chart_names.contains(e.left.name.as_str()) {
            return reference(
                e.left.span,
                format!(
                    "unknown nerve chart `{}` in edge `{}` ({context})",
                    e.left.name, e.name.name
                ),
            );
        }
        if !chart_names.contains(e.right.name.as_str()) {
            return reference(
                e.right.span,
                format!(
                    "unknown nerve chart `{}` in edge `{}` ({context})",
                    e.right.name, e.name.name
                ),
            );
        }
        if edge_endpoints
            .insert(
                e.name.name.as_str(),
                (e.left.name.as_str(), e.right.name.as_str()),
            )
            .is_some()
        {
            return duplicate(
                e.name.span,
                format!("duplicate nerve edge `{}` in {context}", e.name.name),
            );
        }
        edges.push(ShigureNerveEdge {
            name: e.name.name.clone(),
            left: e.left.name.clone(),
            right: e.right.name.clone(),
            span: e.span,
        });
    }

    let mut face_names = HashSet::new();
    let mut faces = Vec::with_capacity(raw.faces.len());
    for f in &raw.faces {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if f.name.name == "none" {
            return p4_type_err(f.name.span, "nerve face name `none` is reserved");
        }
        if !face_names.insert(f.name.name.as_str()) {
            return duplicate(
                f.name.span,
                format!("duplicate nerve face `{}` in {context}", f.name.name),
            );
        }
        let Some(&(l0, r0)) = edge_endpoints.get(f.e0.name.as_str()) else {
            return reference(
                f.e0.span,
                format!(
                    "unknown nerve edge `{}` in face `{}` ({context})",
                    f.e0.name, f.name.name
                ),
            );
        };
        let Some(&(l1, r1)) = edge_endpoints.get(f.e1.name.as_str()) else {
            return reference(
                f.e1.span,
                format!(
                    "unknown nerve edge `{}` in face `{}` ({context})",
                    f.e1.name, f.name.name
                ),
            );
        };
        let Some(&(l2, r2)) = edge_endpoints.get(f.e2.name.as_str()) else {
            return reference(
                f.e2.span,
                format!(
                    "unknown nerve edge `{}` in face `{}` ({context})",
                    f.e2.name, f.name.name
                ),
            );
        };
        if l0 != l1 || r0 != l2 || r1 != r2 {
            return p4_type_err(
                f.span,
                format!(
                    "nerve face `{}` violates K1 endpoint equations in {context}: e0=({l0},{r0}), e1=({l1},{r1}), e2=({l2},{r2})",
                    f.name.name
                ),
            );
        }
        faces.push(ShigureNerveFace {
            name: f.name.name.clone(),
            e0: f.e0.name.clone(),
            e1: f.e1.name.clone(),
            e2: f.e2.name.clone(),
            span: f.span,
        });
    }

    Ok(ShigureSupportedNerve {
        charts,
        edges,
        faces,
        span: raw.span,
    })
}

fn literal_domain(lit: &ShigureScalarLit) -> ShigureCoeffDomain {
    match lit {
        ShigureScalarLit::Int(_) => ShigureCoeffDomain::Z,
        ShigureScalarLit::Rat { .. } => ShigureCoeffDomain::Q,
        ShigureScalarLit::Fp { modulus, .. } => ShigureCoeffDomain::Fp(modulus.clone()),
    }
}

fn check_partition<E: InputError>(
    raw: &[Vec<Ident>],
    sources: &HashSet<&str>,
    span: Span,
    context: &str,
) -> CResult<Vec<Vec<String>>, E> {
    let mut seen = HashSet::new();
    let mut out = Vec::with_capacity(raw.len());
    for block in raw {
        if block.is_empty() {
            return p4_type_err(
                span,
                format!("partition block must be non-empty in {context}"),
            );
        }
        let mut b = Vec::with_capacity(block.len());
        for s in block {
            if !sources.contains(s.name.as_str()) {
                return reference(s.span, format!("unknown source `{}` in {context}", s.name));
            }
            if !seen.insert(s.name.as_str()) {
                return duplicate(
                    s.span,
                    format!(
                        "source `{}` appears in multiple blocks in {context}",
                        s.name
                    ),
                );
            }
            b.push(s.name.clone());
        }
        out.push(b);
    }
    if seen.len() != sources.len() {
        return p4_type_err(
            span,
            format!("partition must cover every source in {context}"),
        );
    }
    Ok(out)
}

fn check_coarsening<E: InputError>(
    fine: &[Vec<String>],
    coarse: &[Vec<String>],
    span: Span,
    context: &str,
) -> CResult<(), E> {
    let mut coarse_of: HashMap<&str, usize> = HashMap::new();
    for (ci, block) in coarse.iter().enumerate() {
        for s in block {
            coarse_of.insert(s.as_str(), ci);
        }
    }
    for fblock in fine {
        let first = coarse_of[fblock[0].as_str()];
        if fblock.iter().any(|s| coarse_of[s.as_str()] != first) {
            return p4_type_err(
                span,
                format!("coarse partition is not a coarsening of fine partition in {context}"),
            );
        }
    }
    Ok(())
}

pub(super) fn check_diagnostics<E: InputError>(
    raw: &RawDiagnosticsTask,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    control: &Control,
) -> CResult<ShigureDiagnosticsTask, E> {
    let name = full(reading_name, &[&raw.name.name]);
    let ctx = format!("`shigure diagnostics {name}`");
    let diagnostic_coeff = check_coeff_domain(&raw.diagnostic_coeff, control)?;
    let origins = check_p4_origins(&raw.origins, raw.span, &ctx)?;
    if let Some(0) = raw.max_partitions {
        return p4_type_err(raw.span, format!("`max_partitions` must be >= 1 in {ctx}"));
    }

    let (readout, source_vec, target_vec, law_names, poly_meta) = match &raw.readout {
        RawDiagnosticsReadout::Static {
            sources,
            targets,
            reading,
            laws,
            span,
        } => {
            let src_vec = check_p4_unique_idents(sources, "source", &ctx)?;
            let tgt_vec = check_p4_unique_idents(targets, "target", &ctx)?;
            let src_set: HashSet<&str> = src_vec.iter().map(String::as_str).collect();
            let tgt_set: HashSet<&str> = tgt_vec.iter().map(String::as_str).collect();
            let mut q_seen = HashSet::new();
            let mut q_img = HashSet::new();
            let mut checked_reading = Vec::with_capacity(reading.len());
            for (s, t, _) in reading {
                if !src_set.contains(s.name.as_str()) {
                    return reference(s.span, format!("unknown source `{}` in reading", s.name));
                }
                if !tgt_set.contains(t.name.as_str()) {
                    return reference(t.span, format!("unknown target `{}` in reading", t.name));
                }
                if !q_seen.insert(s.name.as_str()) {
                    return duplicate(s.span, format!("duplicate reading source `{}`", s.name));
                }
                q_img.insert(t.name.as_str());
                checked_reading.push((s.name.clone(), t.name.clone()));
            }
            if q_seen.len() != src_set.len() {
                return p4_type_err(*span, format!("reading must assign every source in {ctx}"));
            }
            if q_img.len() != tgt_set.len() {
                return p4_type_err(
                    *span,
                    format!("reading must be surjective onto targets in {ctx}"),
                );
            }
            let mut l_names = HashSet::new();
            let mut checked_laws = Vec::with_capacity(laws.len());
            for law in laws {
                if !l_names.insert(law.law_name.name.clone()) {
                    return duplicate(
                        law.law_name.span,
                        format!("duplicate law `{}` in {ctx}", law.law_name.name),
                    );
                }
                let mut v_seen = HashSet::new();
                let mut law_dom: Option<ShigureCoeffDomain> = None;
                let mut checked_vals = Vec::with_capacity(law.values.len());
                for (s, lit, v_span) in &law.values {
                    if !src_set.contains(s.name.as_str()) {
                        return reference(
                            s.span,
                            format!("unknown source `{}` in law `{}`", s.name, law.law_name.name),
                        );
                    }
                    if !v_seen.insert(s.name.as_str()) {
                        return duplicate(
                            s.span,
                            format!(
                                "duplicate source `{}` in law `{}`",
                                s.name, law.law_name.name
                            ),
                        );
                    }
                    let ld = literal_domain(lit);
                    check_scalar_lit(lit, &ld, *v_span, control)?;
                    if let Some(ref exp) = law_dom {
                        if exp != &ld {
                            return p4_type_err(
                                *v_span,
                                format!(
                                    "inconsistent scalar domain in static law `{}`",
                                    law.law_name.name
                                ),
                            );
                        }
                    } else {
                        law_dom = Some(ld);
                    }
                    checked_vals.push((s.name.clone(), lit.clone()));
                }
                if v_seen.len() != src_set.len() {
                    return p4_type_err(
                        law.span,
                        format!(
                            "static law `{}` must assign every source",
                            law.law_name.name
                        ),
                    );
                }
                checked_laws.push(ShigureStaticLawReadout {
                    law_name: law.law_name.name.clone(),
                    values: checked_vals,
                    span: law.span,
                });
            }
            (
                ShigureDiagnosticsReadout::Static {
                    sources: src_vec.clone(),
                    targets: tgt_vec.clone(),
                    reading: checked_reading,
                    laws: checked_laws,
                    span: *span,
                },
                src_vec,
                tgt_vec,
                l_names,
                None,
            )
        }
        RawDiagnosticsReadout::Polynomial {
            base_domain,
            base_vars,
            base_relations,
            sources,
            laws,
            span,
        } => {
            let bdom = check_coeff_domain(base_domain, control)?;
            let bvars = check_p4_unique_idents(base_vars, "base_var", &ctx)?;
            let bv_set: HashSet<&str> = bvars.iter().map(String::as_str).collect();
            let brels = check_named_polys_in_scope(
                base_relations,
                &bdom,
                &bv_set,
                &format!("{ctx} base_relations"),
                control,
            )?;
            let src_vec = check_p4_unique_idents(sources, "source", &ctx)?;
            let src_set: HashSet<&str> = src_vec.iter().map(String::as_str).collect();
            let mut l_names = HashSet::new();
            let mut checked_laws = Vec::with_capacity(laws.len());
            for law in laws {
                if !l_names.insert(law.law_name.name.clone()) {
                    return duplicate(
                        law.law_name.span,
                        format!("duplicate law `{}` in {ctx}", law.law_name.name),
                    );
                }
                let mut v_seen = HashSet::new();
                let mut checked_vals = Vec::with_capacity(law.values.len());
                for (s, val, v_span) in &law.values {
                    if !src_set.contains(s.name.as_str()) {
                        return reference(
                            s.span,
                            format!("unknown source `{}` in law `{}`", s.name, law.law_name.name),
                        );
                    }
                    if !v_seen.insert(s.name.as_str()) {
                        return duplicate(
                            s.span,
                            format!(
                                "duplicate source `{}` in law `{}`",
                                s.name, law.law_name.name
                            ),
                        );
                    }
                    let checked_val = match val {
                        RawPolyOrObserved::Poly(expr) => {
                            check_poly_literals(
                                expr,
                                LiteralDomainRule::Exact(&bdom),
                                *v_span,
                                control,
                            )?;
                            check_poly_vars(
                                expr,
                                &bv_set,
                                *v_span,
                                &format!("poly law `{}` source `{}`", law.law_name.name, s.name),
                                control,
                            )?;
                            ShigurePolyOrObserved::Poly(expr.clone())
                        }
                        RawPolyOrObserved::ObservedField { field, span: fspan } => {
                            let ShigureCoordBinding::ObservedField {
                                entity,
                                field: field_full,
                                span: resolved_span,
                            } = resolve_observed_field(
                                field,
                                *fspan,
                                &bdom,
                                &checker.imports[r_idx],
                                checker.definitions,
                            )?
                            else {
                                unreachable!("resolve_observed_field always returns ObservedField");
                            };
                            ShigurePolyOrObserved::ObservedField {
                                entity,
                                field: field_full,
                                span: resolved_span,
                            }
                        }
                        RawPolyOrObserved::Missing(_) => ShigurePolyOrObserved::Missing,
                    };
                    checked_vals.push((s.name.clone(), checked_val));
                }
                if v_seen.len() != src_set.len() {
                    return p4_type_err(
                        law.span,
                        format!("poly law `{}` must assign every source", law.law_name.name),
                    );
                }
                checked_laws.push(ShigurePolyLawReadout {
                    law_name: law.law_name.name.clone(),
                    values: checked_vals,
                    span: law.span,
                });
            }
            (
                ShigureDiagnosticsReadout::Polynomial {
                    base_domain: bdom.clone(),
                    base_vars: bvars.clone(),
                    base_relations: brels,
                    sources: src_vec.clone(),
                    laws: checked_laws,
                    span: *span,
                },
                src_vec.clone(),
                src_vec,
                l_names,
                Some((bvars, bdom)),
            )
        }
    };

    let tgt_set: HashSet<&str> = target_vec.iter().map(String::as_str).collect();
    let nerve = check_supported_nerve(&raw.nerve, &tgt_set, &ctx, control)?;

    let coeff_change = raw
        .coeff_change
        .as_ref()
        .map(|cc| {
            let target_domain = check_coeff_domain(&cc.target_domain, control)?;
            let explicit_z_complex = cc
                .explicit_z_complex
                .as_ref()
                .map(|ez| {
                    if ez.d0.len() != ez.dim1 || ez.d0.iter().any(|row| row.len() != ez.dim0) {
                        return p4_type_err(ez.span, "explicit_z_complex d0 shape mismatch");
                    }
                    if let Some(coc) = &ez.designated_cocycle
                        && coc.len() != ez.dim1
                    {
                        return p4_type_err(
                            ez.span,
                            "explicit_z_complex designated_cocycle length mismatch",
                        );
                    }
                    Ok::<_, E>(ShigureExplicitZComplex {
                        dim0: ez.dim0,
                        dim1: ez.dim1,
                        d0: ez.d0.clone(),
                        designated_cocycle: ez.designated_cocycle.clone(),
                        span: ez.span,
                    })
                })
                .transpose()?;
            Ok::<_, E>(ShigureCoeffChangeComparison {
                target_domain,
                compare_codomain_regeneration: cc.compare_codomain_regeneration,
                explicit_z_complex,
                span: cc.span,
            })
        })
        .transpose()?;

    let src_set: HashSet<&str> = source_vec.iter().map(String::as_str).collect();
    let mut col_labels = HashSet::new();
    let mut collisions = Vec::with_capacity(raw.collisions.len());
    for col in &raw.collisions {
        if col.label.trim().is_empty() {
            return p4_type_err(col.span, "collision label must be non-empty");
        }
        if !col_labels.insert(col.label.as_str()) {
            return duplicate(
                col.span,
                format!("duplicate collision `{}` in {ctx}", col.label),
            );
        }
        if !law_names.contains(&col.law_name.name) {
            return reference(
                col.law_name.span,
                format!(
                    "unknown law `{}` in collision `{}`",
                    col.law_name.name, col.label
                ),
            );
        }
        let fine = check_partition(&col.fine_partition, &src_set, col.span, &col.label)?;
        let coarse = check_partition(&col.coarse_partition, &src_set, col.span, &col.label)?;
        check_coarsening(&fine, &coarse, col.span, &col.label)?;
        let mut alt_paths = Vec::with_capacity(col.alternative_merge_paths.len());
        for path in &col.alternative_merge_paths {
            let mut prev = &fine;
            let mut checked_path = Vec::with_capacity(path.len());
            for step in path {
                let checked_step = check_partition(step, &src_set, col.span, &col.label)?;
                check_coarsening(prev, &checked_step, col.span, &col.label)?;
                checked_path.push(checked_step);
                prev = checked_path.last().expect("non-empty step");
            }
            check_coarsening(prev, &coarse, col.span, &col.label)?;
            alt_paths.push(checked_path);
        }
        collisions.push(ShigureCollisionComparison {
            label: col.label.clone(),
            law_name: col.law_name.name.clone(),
            fine_partition: fine,
            coarse_partition: coarse,
            alternative_merge_paths: alt_paths,
            span: col.span,
        });
    }

    let r_point_probe = raw
        .r_point_probe
        .as_ref()
        .map(|rp| {
            let Some((ref bvars, ref bdom)) = poly_meta else {
                return p4_type_err(rp.span, "`r_point_probe` requires `poly_readout`");
            };
            if rp.ring_max_deg == 0 {
                return p4_type_err(rp.span, "`r_point_probe` ring_max_deg must be >= 1");
            }
            let Some(expected_len) = rp.ring_max_deg.checked_add(1) else {
                return p4_type_err(rp.span, "ring_max_deg overflow");
            };
            let mut pt_labels = HashSet::new();
            let mut points = Vec::with_capacity(rp.points.len());
            for pt in &rp.points {
                if pt.label.trim().is_empty() {
                    return p4_type_err(pt.span, "r_point label must be non-empty");
                }
                if !pt_labels.insert(pt.label.as_str()) {
                    return duplicate(pt.span, format!("duplicate r_point `{}`", pt.label));
                }
                let coords = check_p4_coord_vec_map(
                    &pt.coords,
                    bvars,
                    expected_len,
                    bdom,
                    r_idx,
                    checker,
                    pt.span,
                    "base_var",
                    &format!("r_point `{}`", pt.label),
                    control,
                )?;
                points.push(ShigureNamedRPoint {
                    label: pt.label.clone(),
                    coords,
                    span: pt.span,
                });
            }
            Ok::<_, E>(ShigureRPointProbe {
                ring_var: rp.ring_var.name.clone(),
                ring_max_deg: rp.ring_max_deg,
                points,
                span: rp.span,
            })
        })
        .transpose()?;

    let dimension_realization = raw
        .dimension_realization
        .as_ref()
        .map(|dr| {
            let bdom = check_coeff_domain(&dr.base_domain, control)?;
            let bvars = check_p4_unique_idents(&dr.base_vars, "base_var", "dimension_realization")?;
            let bv_set: HashSet<&str> = bvars.iter().map(String::as_str).collect();
            let vanishing_polys = check_named_polys_in_scope(
                &dr.vanishing_polys,
                &bdom,
                &bv_set,
                "dimension_realization vanishing",
                control,
            )?;
            let mut inv_list = check_named_polys_in_scope(
                std::slice::from_ref(&dr.invertible_poly),
                &bdom,
                &bv_set,
                "dimension_realization invertible",
                control,
            )?;
            let invertible_poly = inv_list.pop().expect("single invertible_poly");
            let mut pt_labels = HashSet::new();
            let mut probe_points = Vec::with_capacity(dr.probe_points.len());
            for pt in &dr.probe_points {
                if pt.label.trim().is_empty() {
                    return p4_type_err(pt.span, "probe point label must be non-empty");
                }
                if !pt_labels.insert(pt.label.as_str()) {
                    return duplicate(pt.span, format!("duplicate probe point `{}`", pt.label));
                }
                let coords = check_p4_coord_scalar_map(
                    &pt.coords,
                    &bvars,
                    &bdom,
                    r_idx,
                    checker,
                    pt.span,
                    "base_var",
                    &format!("probe `{}`", pt.label),
                    control,
                )?;
                probe_points.push(ShigureNamedBasePoint {
                    label: pt.label.clone(),
                    coords,
                    span: pt.span,
                });
            }
            Ok::<_, E>(ShigureDimensionRealization {
                base_domain: bdom,
                base_vars: bvars,
                vanishing_polys,
                invertible_poly,
                probe_points,
                span: dr.span,
            })
        })
        .transpose()?;

    Ok(ShigureDiagnosticsTask {
        name,
        reading: reading_name.to_owned(),
        diagnostic_coeff,
        origins,
        nerve,
        readout,
        coeff_change,
        collisions,
        r_point_probe,
        dimension_realization,
        max_partitions: raw.max_partitions,
        span: raw.span,
    })
}
