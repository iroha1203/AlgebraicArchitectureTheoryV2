//! `shigure lift`・`shigure artin` 宣言の静的意味検査および Phase 4 共通検査ヘルパ（AC2）。

use super::ast_phase3::{
    RawMemberCoordValue, RawOriginRef, ShigureMemberCoordValue, ShigureOriginRef,
};
use super::ast_phase4_lift_artin::*;
use super::check::{
    CResult, CoordCheckCtx, LiteralDomainRule, check_coeff_domain, check_member_coord_value,
    check_poly_literals, check_poly_vars,
};
use super::check_ext_common::check_scalar_lit;
use super::check_family::{check_named_polys_in_scope, check_origin_ref};
use super::*;
use crate::law::ast::{Ident, Span};
use crate::law::check::{Checker, duplicate, full, reference};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy)]
pub(super) struct KeyedBlockMeta<'a> {
    pub(super) span: Span,
    pub(super) kind: &'a str,
    pub(super) context: &'a str,
}

fn check_p4_keyed_entries<T, U, E: InputError>(
    raw: &[(Ident, T, Span)],
    required_keys: &[String],
    meta: KeyedBlockMeta<'_>,
    control: &Control,
    mut check_val: impl FnMut(&str, &T, Span) -> CResult<U, E>,
) -> CResult<Vec<(String, U)>, E> {
    let key_set: HashSet<&str> = required_keys.iter().map(String::as_str).collect();
    let mut seen = HashSet::new();
    let mut out = Vec::with_capacity(raw.len());
    for (k, val, v_span) in raw {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !key_set.contains(k.name.as_str()) {
            return reference(
                k.span,
                format!("unknown {} `{}` in {}", meta.kind, k.name, meta.context),
            );
        }
        if !seen.insert(k.name.as_str()) {
            return duplicate(
                k.span,
                format!("duplicate {} `{}` in {}", meta.kind, k.name, meta.context),
            );
        }
        let checked = check_val(&k.name, val, *v_span)?;
        out.push((k.name.clone(), checked));
    }
    if seen.len() != key_set.len() {
        return p4_type_err(
            meta.span,
            format!("{} must assign every {}", meta.context, meta.kind),
        );
    }
    Ok(out)
}

pub(super) fn check_all_phase4_tasks<E: InputError>(
    checker: &Checker<'_, E>,
    out: &mut CheckedShigureDecls,
    control: &Control,
) -> CResult<(), E> {
    let readings = checker.ast.clone();
    for (r_idx, r) in readings.iter().enumerate() {
        for d in &r.shigure_decls {
            match d {
                ShigureDeclAst::Lift(raw) => {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    let checked = check_lift(raw.as_ref(), r_idx, &r.name.name, checker, control)?;
                    out.lift_tasks.insert(checked.name.clone(), checked);
                }
                ShigureDeclAst::Artin(raw) => {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    let checked = check_artin(raw.as_ref(), r_idx, &r.name.name, checker, control)?;
                    out.artin_tasks.insert(checked.name.clone(), checked);
                }
                ShigureDeclAst::Diagnostics(raw) => {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    let checked = super::check_phase4_diagnostics::check_diagnostics(
                        raw.as_ref(),
                        r_idx,
                        &r.name.name,
                        checker,
                        control,
                    )?;
                    out.diagnostics_tasks.insert(checked.name.clone(), checked);
                }
                ShigureDeclAst::Atlas(raw) => {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    let checked = super::check_phase4_atlas::check_atlas(
                        raw.as_ref(),
                        r_idx,
                        &r.name.name,
                        checker,
                        control,
                    )?;
                    out.atlas_tasks.insert(checked.name.clone(), checked);
                }
                _ => {}
            }
        }
    }
    Ok(())
}

pub(super) fn p4_type_err<T, E: InputError>(span: Span, msg: impl Into<String>) -> CResult<T, E> {
    Err(Box::new(Issue::law(Code::Type, span, msg)).into())
}

pub(super) fn check_p4_origins<E: InputError>(
    raw: &[RawOriginRef],
    span: Span,
    context: &str,
) -> CResult<Vec<ShigureOriginRef>, E> {
    if raw.is_empty() {
        return p4_type_err(span, format!("missing `origin` in {context}"));
    }
    raw.iter().map(|o| check_origin_ref(o, context)).collect()
}

pub(super) fn check_p4_unique_idents<E: InputError>(
    items: &[Ident],
    kind: &str,
    context: &str,
) -> CResult<Vec<String>, E> {
    let mut seen = HashSet::new();
    let mut out = Vec::with_capacity(items.len());
    for id in items {
        if !seen.insert(id.name.as_str()) {
            return duplicate(
                id.span,
                format!("duplicate {kind} `{}` in {context}", id.name),
            );
        }
        out.push(id.name.clone());
    }
    Ok(out)
}

pub(super) fn check_p4_coord_vec<E: InputError>(
    raw: &[RawMemberCoordValue],
    expected_len: usize,
    ctx: &CoordCheckCtx<'_, '_, E>,
    span: Span,
    context: &str,
) -> CResult<Vec<ShigureMemberCoordValue>, E> {
    if raw.len() != expected_len {
        return p4_type_err(
            span,
            format!(
                "{context} has {} coordinates, expected {expected_len}",
                raw.len()
            ),
        );
    }
    raw.iter()
        .map(|v| check_member_coord_value(v, ctx, span))
        .collect()
}

pub(super) fn check_p4_coord_scalar_map<E: InputError>(
    raw: &[(Ident, RawMemberCoordValue, Span)],
    required_keys: &[String],
    ctx: &CoordCheckCtx<'_, '_, E>,
    meta: KeyedBlockMeta<'_>,
) -> CResult<Vec<(String, ShigureMemberCoordValue)>, E> {
    check_p4_keyed_entries(raw, required_keys, meta, ctx.control, |_, val, v_span| {
        check_member_coord_value(val, ctx, v_span)
    })
}

pub(super) fn check_p4_coord_vec_map<E: InputError>(
    raw: &[(Ident, Vec<RawMemberCoordValue>, Span)],
    required_keys: &[String],
    expected_len: usize,
    ctx: &CoordCheckCtx<'_, '_, E>,
    meta: KeyedBlockMeta<'_>,
) -> CResult<Vec<(String, Vec<ShigureMemberCoordValue>)>, E> {
    check_p4_keyed_entries(raw, required_keys, meta, ctx.control, |name, vals, v_span| {
        check_p4_coord_vec(vals, expected_len, ctx, v_span, &format!("{} `{name}`", meta.context))
    })
}

pub(super) fn check_p4_poly_assign_map<E: InputError>(
    raw: &[(Ident, ShigurePolyExpr, Span)],
    required_keys: &[String],
    allowed_rhs_vars: &HashSet<&str>,
    coeff_domain: &ShigureCoeffDomain,
    meta: KeyedBlockMeta<'_>,
    control: &Control,
) -> CResult<Vec<(String, ShigurePolyExpr)>, E> {
    check_p4_keyed_entries(raw, required_keys, meta, control, |name, expr, v_span| {
        check_poly_literals(
            expr,
            LiteralDomainRule::Exact(coeff_domain),
            v_span,
            control,
        )?;
        check_poly_vars(
            expr,
            allowed_rhs_vars,
            v_span,
            &format!("{}.{name}", meta.context),
            control,
        )?;
        Ok(expr.clone())
    })
}

// ---- `shigure lift` 検査 ----

fn check_square_zero_spec<E: InputError>(
    raw: &RawSquareZeroSpec,
    coeff_domain: &ShigureCoeffDomain,
    context: &str,
    control: &Control,
) -> CResult<(ShigureSquareZeroSpec, usize, usize), E> {
    match raw {
        RawSquareZeroSpec::TruncatedPoly {
            var_name,
            base_degree,
            span,
        } => {
            let r_dim = base_degree
                .checked_add(1)
                .ok_or_else(|| Box::new(Issue::law(Code::Type, *span, "base_degree overflow")))?;
            let rp_dim = base_degree
                .checked_add(2)
                .ok_or_else(|| Box::new(Issue::law(Code::Type, *span, "base_degree overflow")))?;
            Ok((
                ShigureSquareZeroSpec::TruncatedPoly {
                    var_name: var_name.name.clone(),
                    base_degree: *base_degree,
                    span: *span,
                },
                r_dim,
                rp_dim,
            ))
        }
        RawSquareZeroSpec::ExplicitTable {
            r_prime_basis,
            r_prime_one,
            r_prime_mul,
            r_base_basis,
            r_base_one,
            r_base_mul,
            projection,
            span,
        } => {
            let rpb = check_p4_unique_idents(r_prime_basis, "r_prime_basis", context)?;
            let rbb = check_p4_unique_idents(r_base_basis, "r_base_basis", context)?;
            let rp_dim = rpb.len();
            let r_dim = rbb.len();
            if rp_dim == 0 || r_dim == 0 {
                return p4_type_err(
                    *span,
                    format!("explicit_table bases must be non-empty in {context}"),
                );
            }
            if r_prime_one.len() != rp_dim
                || r_base_one.len() != r_dim
                || r_prime_mul.len() != rp_dim
                || r_prime_mul
                    .iter()
                    .any(|m| m.len() != rp_dim || m.iter().any(|v| v.len() != rp_dim))
                || r_base_mul.len() != r_dim
                || r_base_mul
                    .iter()
                    .any(|m| m.len() != r_dim || m.iter().any(|v| v.len() != r_dim))
                || projection.len() != r_dim
                || projection.iter().any(|row| row.len() != rp_dim)
            {
                return p4_type_err(
                    *span,
                    format!("explicit_table matrix/tensor shape mismatch in {context}"),
                );
            }
            for lit in r_prime_one
                .iter()
                .chain(r_base_one)
                .chain(r_prime_mul.iter().flatten().flatten())
                .chain(r_base_mul.iter().flatten().flatten())
                .chain(projection.iter().flatten())
            {
                check_scalar_lit(lit, coeff_domain, *span, control)?;
            }
            Ok((
                ShigureSquareZeroSpec::ExplicitTable {
                    r_prime_basis: rpb,
                    r_prime_one: r_prime_one.clone(),
                    r_prime_mul: r_prime_mul.clone(),
                    r_base_basis: rbb,
                    r_base_one: r_base_one.clone(),
                    r_base_mul: r_base_mul.clone(),
                    projection: projection.clone(),
                    span: *span,
                },
                r_dim,
                rp_dim,
            ))
        }
    }
}

fn check_lift<E: InputError>(
    raw: &RawLiftTask,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    control: &Control,
) -> CResult<ShigureLiftTask, E> {
    let name = full(reading_name, &[&raw.name.name]);
    let ctx = format!("`shigure lift {name}`");
    let coeff_domain = check_coeff_domain(&raw.domain, control)?;
    let origins = check_p4_origins(&raw.origins, raw.span, &ctx)?;
    let variables = check_p4_unique_idents(&raw.variables, "variable", &ctx)?;
    let (extension, r_dim, rp_dim) =
        check_square_zero_spec(&raw.extension, &coeff_domain, &ctx, control)?;

    let coord_ctx = CoordCheckCtx {
        coeff_domain: &coeff_domain,
        r_idx,
        checker,
        control,
    };

    let var_set: HashSet<&str> = variables.iter().map(String::as_str).collect();
    let mut param_set = HashSet::new();
    let mut ring_params = Vec::with_capacity(raw.ring_params.len());
    for rp in &raw.ring_params {
        if var_set.contains(rp.name.name.as_str()) || !param_set.insert(rp.name.name.as_str()) {
            return duplicate(
                rp.name.span,
                format!(
                    "ring_param `{}` collides with variable or duplicate in {ctx}",
                    rp.name.name
                ),
            );
        }
        let val = check_p4_coord_vec(
            &rp.value_in_r_prime,
            rp_dim,
            &coord_ctx,
            rp.span,
            &format!("{ctx} ring_param `{}`", rp.name.name),
        )?;
        ring_params.push(ShigureRingParam {
            name: rp.name.name.clone(),
            value_in_r_prime: val,
            span: rp.span,
        });
    }

    let mut law_scope: HashSet<&str> = var_set.clone();
    law_scope.extend(param_set.iter().copied());
    let laws = check_named_polys_in_scope(
        &raw.laws,
        &coeff_domain,
        &law_scope,
        &format!("{ctx} laws"),
        control,
    )?;
    let law_names: HashSet<&str> = laws.iter().map(|l| l.name.as_str()).collect();

    let base_point = check_p4_coord_vec_map(
        &raw.base_point,
        &variables,
        r_dim,
        &coord_ctx,
        KeyedBlockMeta {
            span: raw.span,
            kind: "variable",
            context: &format!("{ctx} base_point"),
        },
    )?;
    let ambient_lift = raw
        .ambient_lift
        .as_ref()
        .map(|al| {
            check_p4_coord_vec_map(
                al,
                &variables,
                rp_dim,
                &coord_ctx,
                KeyedBlockMeta {
                    span: raw.span,
                    kind: "variable",
                    context: &format!("{ctx} ambient_lift"),
                },
            )
        })
        .transpose()?;

    let relative_reading = raw
        .relative_reading
        .as_ref()
        .map(|rel| {
            let obs_vars = check_p4_unique_idents(
                &rel.obs_vars,
                "obs_var",
                &format!("{ctx} relative_reading"),
            )?;
            for ov in &obs_vars {
                if param_set.contains(ov.as_str()) {
                    return duplicate(
                        rel.span,
                        format!("obs_var `{ov}` collides with ring_param in {ctx}"),
                    );
                }
            }
            let mut obs_scope: HashSet<&str> = obs_vars.iter().map(String::as_str).collect();
            obs_scope.extend(param_set.iter().copied());
            let obs_laws = check_named_polys_in_scope(
                &rel.obs_laws,
                &coeff_domain,
                &obs_scope,
                &format!("{ctx} obs_laws"),
                control,
            )?;
            let reading_map = check_p4_poly_assign_map(
                &rel.reading_map,
                &obs_vars,
                &law_scope,
                &coeff_domain,
                KeyedBlockMeta {
                    span: rel.span,
                    kind: "obs_var",
                    context: &format!("{ctx} reading_map"),
                },
                control,
            )?;
            let designated_obs_lift = check_p4_coord_vec_map(
                &rel.designated_obs_lift,
                &obs_vars,
                rp_dim,
                &coord_ctx,
                KeyedBlockMeta {
                    span: rel.span,
                    kind: "obs_var",
                    context: &format!("{ctx} designated_obs_lift"),
                },
            )?;
            let raw_read_diff = rel
                .raw_read_diff
                .as_ref()
                .map(|rr| {
                    if rr.label.trim().is_empty() {
                        return p4_type_err(rr.span, "raw_read_diff label must be non-empty");
                    }
                    check_poly_literals(
                        &rr.expr,
                        LiteralDomainRule::Exact(&coeff_domain),
                        rr.span,
                        control,
                    )?;
                    check_poly_vars(&rr.expr, &law_scope, rr.span, "raw_read_diff", control)?;
                    Ok::<_, E>(ShigureRawReadComparison {
                        label: rr.label.clone(),
                        expr: rr.expr.clone(),
                        negated: rr.negated,
                        span: rr.span,
                    })
                })
                .transpose()?;
            Ok::<_, E>(ShigureRelativeReading {
                obs_vars,
                obs_laws,
                reading_map,
                designated_obs_lift,
                raw_read_diff,
                span: rel.span,
            })
        })
        .transpose()?;

    let declaration_cover = raw
        .declaration_cover
        .as_ref()
        .map(|cov| {
            let mut ctx_vars_map: HashMap<String, HashSet<String>> = HashMap::new();
            let mut contexts = Vec::with_capacity(cov.contexts.len());
            for c in &cov.contexts {
                if ctx_vars_map.contains_key(&c.name.name) {
                    return duplicate(
                        c.name.span,
                        format!("duplicate declaration_context `{}` in {ctx}", c.name.name),
                    );
                }
                let cvars = check_p4_unique_idents(&c.vars, "context var", &ctx)?;
                for v in &cvars {
                    if !var_set.contains(v.as_str()) {
                        return reference(
                            c.span,
                            format!("unknown variable `{v}` in context `{}`", c.name.name),
                        );
                    }
                }
                let claws = check_p4_unique_idents(&c.laws, "context law", &ctx)?;
                for l in &claws {
                    if !law_names.contains(l.as_str()) {
                        return reference(
                            c.span,
                            format!("unknown law `{l}` in context `{}`", c.name.name),
                        );
                    }
                }
                let observations = check_named_polys_in_scope(
                    &c.observations,
                    &coeff_domain,
                    &law_scope,
                    &format!("{ctx} context `{}` obs", c.name.name),
                    control,
                )?;
                ctx_vars_map.insert(c.name.name.clone(), cvars.iter().cloned().collect());
                contexts.push(ShigureDeclarationContext {
                    name: c.name.name.clone(),
                    vars: cvars,
                    laws: claws,
                    observations,
                    span: c.span,
                });
            }
            let two_context_cech = cov
                .two_context_cech
                .as_ref()
                .map(|tc| {
                    let Some(lv) = ctx_vars_map.get(&tc.left_context.name) else {
                        return reference(
                            tc.left_context.span,
                            format!("unknown declaration_context `{}`", tc.left_context.name),
                        );
                    };
                    let Some(rv) = ctx_vars_map.get(&tc.right_context.name) else {
                        return reference(
                            tc.right_context.span,
                            format!("unknown declaration_context `{}`", tc.right_context.name),
                        );
                    };
                    let shared = check_p4_unique_idents(&tc.shared_vars, "shared_var", &ctx)?;
                    for sv in &shared {
                        if !lv.contains(sv) || !rv.contains(sv) {
                            return reference(
                                tc.span,
                                format!(
                                    "shared_var `{sv}` must belong to both `{}` and `{}`",
                                    tc.left_context.name, tc.right_context.name
                                ),
                            );
                        }
                    }
                    Ok::<_, E>(ShigureTwoContextCech {
                        left_context: tc.left_context.name.clone(),
                        right_context: tc.right_context.name.clone(),
                        shared_vars: shared,
                        span: tc.span,
                    })
                })
                .transpose()?;
            Ok::<_, E>(ShigureDeclarationCover {
                contexts,
                two_context_cech,
                span: cov.span,
            })
        })
        .transpose()?;

    let affine_allowed = raw
        .affine_allowed
        .as_ref()
        .map(|aff| {
            let av = check_p4_unique_idents(&aff.allowed_vars, "allowed_var", &ctx)?;
            for v in &av {
                if !var_set.contains(v.as_str()) {
                    return reference(
                        aff.span,
                        format!("unknown variable `{v}` in affine_allowed"),
                    );
                }
            }
            Ok::<_, E>(ShigureAffineAllowed {
                allowed_vars: av,
                finite_displacement: aff.finite_displacement,
                span: aff.span,
            })
        })
        .transpose()?;

    let redundant_comparison = raw
        .redundant_comparison
        .as_ref()
        .map(|rc| {
            let ref_laws = check_named_polys_in_scope(
                &rc.reference_laws,
                &coeff_domain,
                &law_scope,
                &format!("{ctx} redundant_comparison"),
                control,
            )?;
            Ok::<_, E>(ShigureRedundantComparison {
                reference_laws: ref_laws,
                span: rc.span,
            })
        })
        .transpose()?;

    let etale_descent = raw
        .etale_descent
        .as_ref()
        .map(|ed| {
            if ed.degree < 2 {
                return p4_type_err(ed.span, "`etale_descent` degree must be >= 2");
            }
            if ed.base_var.name == ed.cover_var.name {
                return p4_type_err(
                    ed.span,
                    "`etale_descent` base_var and cover_var must be distinct",
                );
            }
            Ok::<_, E>(ShigureFiniteEtaleDescent {
                base_var: ed.base_var.name.clone(),
                cover_var: ed.cover_var.name.clone(),
                degree: ed.degree,
                base_invertible: ed.base_invertible,
                span: ed.span,
            })
        })
        .transpose()?;

    if let Some(0) = raw.max_syzygy_pairs {
        return p4_type_err(raw.span, "`max_syzygy_pairs` must be >= 1");
    }

    Ok(ShigureLiftTask {
        name,
        reading: reading_name.to_owned(),
        coeff_domain,
        origins,
        variables,
        ring_params,
        laws,
        extension,
        base_point,
        ambient_lift,
        relative_reading,
        declaration_cover,
        affine_allowed,
        redundant_comparison,
        etale_descent,
        max_syzygy_pairs: raw.max_syzygy_pairs,
        span: raw.span,
    })
}

// ---- `shigure artin` 検査 ----

fn check_artin<E: InputError>(
    raw: &RawArtinTask,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    control: &Control,
) -> CResult<ShigureArtinTask, E> {
    let name = full(reading_name, &[&raw.name.name]);
    let ctx = format!("`shigure artin {name}`");
    let coeff_domain = check_coeff_domain(&raw.domain, control)?;
    let origins = check_p4_origins(&raw.origins, raw.span, &ctx)?;
    if raw.max_order == 0 {
        return p4_type_err(raw.span, format!("`max_order` must be >= 1 in {ctx}"));
    }
    if let Some(0) = raw.max_artin_dim {
        return p4_type_err(raw.span, format!("`max_artin_dim` must be >= 1 in {ctx}"));
    }
    let obs_vars = check_p4_unique_idents(&raw.obs_vars, "obs_var", &ctx)?;
    let obs_set: HashSet<&str> = obs_vars.iter().map(String::as_str).collect();

    let obs_relations = check_named_polys_in_scope(
        &raw.obs_relations,
        &coeff_domain,
        &obs_set,
        &format!("{ctx} obs_relations"),
        control,
    )?;

    // 非循環依存順検査（F1）: aux_j は obs_vars と先行 aux のみ参照可。
    let mut available: HashSet<&str> = obs_set.clone();
    let mut aux_defs = Vec::with_capacity(raw.aux_defs.len());
    for aux in &raw.aux_defs {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if available.contains(aux.name.name.as_str()) {
            return duplicate(
                aux.name.span,
                format!(
                    "aux_def `{}` collides with earlier variable in {ctx}",
                    aux.name.name
                ),
            );
        }
        check_poly_literals(
            &aux.expr,
            LiteralDomainRule::Exact(&coeff_domain),
            aux.span,
            control,
        )?;
        check_poly_vars(
            &aux.expr,
            &available,
            aux.span,
            &format!(
                "{ctx} aux_def `{}` (acyclic dependency order)",
                aux.name.name
            ),
            control,
        )?;
        available.insert(aux.name.name.as_str());
        aux_defs.push(ShigureAuxiliaryDef {
            name: aux.name.name.clone(),
            expr: aux.expr.clone(),
            span: aux.span,
        });
    }

    let extra_laws = check_named_polys_in_scope(
        &raw.extra_laws,
        &coeff_domain,
        &available,
        &format!("{ctx} extra_laws"),
        control,
    )?;

    let coord_ctx = CoordCheckCtx {
        coeff_domain: &coeff_domain,
        r_idx,
        checker,
        control,
    };
    let base_point = check_p4_coord_scalar_map(
        &raw.base_point,
        &obs_vars,
        &coord_ctx,
        KeyedBlockMeta {
            span: raw.span,
            kind: "obs_var",
            context: &format!("{ctx} base_point"),
        },
    )?;

    let composite_stage = raw
        .composite_stage
        .as_ref()
        .map(|cs| {
            let mut stage_avail = available.clone();
            let mut stage_aux = Vec::with_capacity(cs.aux_defs.len());
            for aux in &cs.aux_defs {
                E::checkpoint(control, Checkpoint::LawSemantics)?;
                if stage_avail.contains(aux.name.name.as_str()) {
                    return duplicate(
                        aux.name.span,
                        format!(
                            "composite_stage aux_def `{}` collides with earlier variable in {ctx}",
                            aux.name.name
                        ),
                    );
                }
                check_poly_literals(
                    &aux.expr,
                    LiteralDomainRule::Exact(&coeff_domain),
                    aux.span,
                    control,
                )?;
                check_poly_vars(
                    &aux.expr,
                    &stage_avail,
                    aux.span,
                    &format!("{ctx} composite_stage aux_def `{}`", aux.name.name),
                    control,
                )?;
                stage_avail.insert(aux.name.name.as_str());
                stage_aux.push(ShigureAuxiliaryDef {
                    name: aux.name.name.clone(),
                    expr: aux.expr.clone(),
                    span: aux.span,
                });
            }
            let stage_laws = check_named_polys_in_scope(
                &cs.extra_laws,
                &coeff_domain,
                &stage_avail,
                &format!("{ctx} composite_stage extra_laws"),
                control,
            )?;
            Ok::<_, E>(ShigureCompositeStage {
                aux_defs: stage_aux,
                extra_laws: stage_laws,
                span: cs.span,
            })
        })
        .transpose()?;

    let base_change = raw
        .base_change
        .as_ref()
        .map(|bc| {
            let target_domain = check_coeff_domain(&bc.target_domain, control)?;
            if let Some(0) = bc.test_order {
                return p4_type_err(bc.span, "`base_change` test_order must be >= 1");
            }
            Ok::<_, E>(ShigureArtinBaseChange {
                target_domain,
                test_order: bc.test_order,
                span: bc.span,
            })
        })
        .transpose()?;

    Ok(ShigureArtinTask {
        name,
        reading: reading_name.to_owned(),
        coeff_domain,
        origins,
        obs_vars,
        obs_relations,
        aux_defs,
        extra_laws,
        base_point,
        max_order: raw.max_order,
        max_artin_dim: raw.max_artin_dim,
        composite_stage,
        base_change,
        non_noetherian_infinite: raw.non_noetherian_infinite,
        span: raw.span,
    })
}
