//! `shigure family` 宣言の静的意味検査（変数・由来・観測参照・保存/操作列整合）。

use super::ast_phase3::*;
use super::check::{
    CResult, DeclCategory, LiteralDomainRule, check_coeff_domain, check_poly_literals,
    check_poly_vars, check_presentation_vars, resolve_observed_field, resolve_shigure_ref,
};
use super::check_ext_common::check_scalar_lit;
use super::*;
use crate::law::ast::{Ident, Span};
use crate::law::check::{Checker, duplicate, full, reference};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;
use std::collections::{BTreeMap, HashMap, HashSet};

pub(super) fn check_origin_ref<E: InputError>(
    raw: &RawOriginRef,
    context: &str,
) -> CResult<ShigureOriginRef, E> {
    match raw {
        RawOriginRef::Explicit { kind, id, span } => {
            if id.trim().is_empty() {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    *span,
                    format!("origin id must be non-empty in {context}"),
                ))
                .into());
            }
            Ok(ShigureOriginRef::Explicit {
                kind: *kind,
                id: id.clone(),
                span: *span,
            })
        }
        RawOriginRef::ArchMap { id, span } => {
            if id.trim().is_empty() {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    *span,
                    format!("archmap origin id must be non-empty in {context}"),
                ))
                .into());
            }
            Ok(ShigureOriginRef::ArchMap {
                id: id.clone(),
                span: *span,
            })
        }
    }
}

pub(super) fn check_named_polys_in_scope<E: InputError>(
    raw_items: &[RawNamedPoly],
    coeff_domain: &ShigureCoeffDomain,
    allowed_vars: &HashSet<&str>,
    scope_name: &str,
    control: &Control,
) -> CResult<Vec<ShigureNamedPoly>, E> {
    let mut seen = HashSet::new();
    let mut out = Vec::with_capacity(raw_items.len());
    for item in raw_items {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !seen.insert(item.name.name.clone()) {
            return duplicate(
                item.name.span,
                format!("duplicate polynomial `{}` in {scope_name}", item.name.name),
            );
        }
        check_poly_literals(
            &item.expr,
            LiteralDomainRule::Exact(coeff_domain),
            item.span,
            control,
        )?;
        let ctx = format!("{scope_name}.{}", item.name.name);
        check_poly_vars(&item.expr, allowed_vars, item.span, &ctx, control)?;
        out.push(ShigureNamedPoly {
            name: item.name.name.clone(),
            expr: item.expr.clone(),
            span: item.span,
        });
    }
    Ok(out)
}

fn collect_unique_vars<E: InputError>(
    vars: &[Ident],
    context: &str,
    disjoint_against: &[&HashSet<String>],
) -> CResult<Vec<String>, E> {
    let mut seen = HashSet::new();
    let mut out = Vec::with_capacity(vars.len());
    for v in vars {
        if !seen.insert(v.name.clone()) {
            return duplicate(
                v.span,
                format!("duplicate variable `{}` in {context}", v.name),
            );
        }
        if disjoint_against.iter().any(|s| s.contains(&v.name)) {
            return duplicate(
                v.span,
                format!(
                    "variable `{}` collides across variable namespaces in {context}",
                    v.name
                ),
            );
        }
        out.push(v.name.clone());
    }
    Ok(out)
}

#[allow(clippy::too_many_arguments)]
fn check_member_assignments<E: InputError>(
    raw_assigns: &[(Ident, RawMemberCoordValue, Span)],
    expected_vars: &[String],
    coeff_domain: &ShigureCoeffDomain,
    r_idx: usize,
    checker: &Checker<'_, E>,
    member_span: Span,
    context: &str,
    control: &Control,
) -> CResult<BTreeMap<String, ShigureMemberCoordValue>, E> {
    let expected_set: HashSet<&str> = expected_vars.iter().map(String::as_str).collect();
    let mut out = BTreeMap::new();
    for (var, val, span) in raw_assigns {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !expected_set.contains(var.name.as_str()) {
            return reference(
                var.span,
                format!("unknown coordinate `{}` in {context}", var.name),
            );
        }
        if out.contains_key(&var.name) {
            return duplicate(
                var.span,
                format!("duplicate assignment for `{}` in {context}", var.name),
            );
        }
        let checked_val = match val {
            RawMemberCoordValue::Literal(lit) => {
                check_scalar_lit(lit, coeff_domain, *span, control)?;
                ShigureMemberCoordValue::Literal(lit.clone())
            }
            RawMemberCoordValue::ObservedField {
                field,
                span: f_span,
            } => {
                let binding = resolve_observed_field(
                    field,
                    *f_span,
                    coeff_domain,
                    &checker.imports[r_idx],
                    checker.definitions,
                )?;
                match binding {
                    ShigureCoordBinding::ObservedField {
                        entity,
                        field,
                        span,
                    } => ShigureMemberCoordValue::ObservedField {
                        entity,
                        field,
                        span,
                    },
                    ShigureCoordBinding::Symbolic => {
                        return Err(Box::new(Issue::law(
                            Code::Type,
                            *f_span,
                            "observed binding could not be resolved",
                        ))
                        .into());
                    }
                }
            }
            RawMemberCoordValue::Missing(_) => ShigureMemberCoordValue::Missing,
        };
        out.insert(var.name.clone(), checked_val);
    }
    for req in expected_vars {
        if !out.contains_key(req) {
            return Err(Box::new(Issue::law(
                Code::Type,
                member_span,
                format!("missing assignment for `{req}` in {context}"),
            ))
            .into());
        }
    }
    Ok(out)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_family<E: InputError>(
    raw: &RawFamilySpec,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span, usize)>,
    decls: &CheckedShigureDecls,
    edges: &mut Vec<(usize, usize, Span)>,
    control: &Control,
) -> CResult<ShigureFamilySpec, E> {
    let full_name = full(reading_name, &[&raw.name.name]);
    let coeff_domain = check_coeff_domain(&raw.domain, control)?;

    let u_vars = collect_unique_vars(
        &raw.realizations.u_vars,
        &format!("{full_name}.u_vars"),
        &[],
    )?;
    let u_owned: HashSet<String> = u_vars.iter().cloned().collect();
    let b_vars = collect_unique_vars(
        &raw.realizations.b_vars,
        &format!("{full_name}.b_vars"),
        &[&u_owned],
    )?;
    let b_owned: HashSet<String> = b_vars.iter().cloned().collect();
    let c_vars = collect_unique_vars(
        &raw.candidates.c_vars,
        &format!("{full_name}.c_vars"),
        &[&u_owned, &b_owned],
    )?;
    let c_owned: HashSet<String> = c_vars.iter().cloned().collect();

    let u_set: HashSet<&str> = u_vars.iter().map(String::as_str).collect();
    let c_set: HashSet<&str> = c_vars.iter().map(String::as_str).collect();

    if raw.realizations.reading_q.len() != b_vars.len() {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw.realizations.span,
            format!(
                "`reading_q` length ({}) must match `b_vars` length ({}) in `{full_name}`",
                raw.realizations.reading_q.len(),
                b_vars.len()
            ),
        ))
        .into());
    }
    for (idx, expr) in raw.realizations.reading_q.iter().enumerate() {
        check_poly_literals(
            expr,
            LiteralDomainRule::Exact(&coeff_domain),
            raw.realizations.span,
            control,
        )?;
        check_poly_vars(
            expr,
            &u_set,
            raw.realizations.span,
            &format!("{full_name}.reading_q[{idx}]"),
            control,
        )?;
    }

    if raw.candidates.pi.len() != b_vars.len() {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw.candidates.span,
            format!(
                "`pi` length ({}) must match `b_vars` length ({}) in `{full_name}`",
                raw.candidates.pi.len(),
                b_vars.len()
            ),
        ))
        .into());
    }
    for (idx, expr) in raw.candidates.pi.iter().enumerate() {
        check_poly_literals(
            expr,
            LiteralDomainRule::Exact(&coeff_domain),
            raw.candidates.span,
            control,
        )?;
        check_poly_vars(
            expr,
            &c_set,
            raw.candidates.span,
            &format!("{full_name}.pi[{idx}]"),
            control,
        )?;
    }

    let real_space = match &raw.realizations.space {
        RawRealizationSpace::FiniteMembers { members, .. } => {
            let mut ids = HashSet::new();
            let mut checked = Vec::with_capacity(members.len());
            for m in members {
                E::checkpoint(control, Checkpoint::LawSemantics)?;
                if !ids.insert(m.id.name.clone()) {
                    return duplicate(
                        m.id.span,
                        format!(
                            "duplicate realization member `{}` in `{full_name}`",
                            m.id.name
                        ),
                    );
                }
                let origin = check_origin_ref(&m.origin, &format!("{full_name}.{}", m.id.name))?;
                let assignments = check_member_assignments(
                    &m.assignments,
                    &u_vars,
                    &coeff_domain,
                    r_idx,
                    checker,
                    m.span,
                    &format!("{full_name}.{}", m.id.name),
                    control,
                )?;
                let presentation = match &m.presentation {
                    Some(qname) => {
                        let p_name = resolve_shigure_ref(
                            qname,
                            DeclCategory::Presentation,
                            r_idx,
                            reading_name,
                            checker,
                            index,
                            edges,
                        )?;
                        let pres = &decls.presentations[&p_name];
                        if pres.coeff_domain != coeff_domain {
                            return Err(Box::new(Issue::law(
                                Code::Type,
                                m.span,
                                format!("realization presentation `{p_name}` coefficient domain does not match `{full_name}`"),
                            ))
                            .into());
                        }
                        check_presentation_vars(pres, None, control)?;
                        Some(p_name)
                    }
                    None => None,
                };
                checked.push(ShigureRealizationMember {
                    id: m.id.name.clone(),
                    assignments,
                    is_raw_candidate: m.is_raw_candidate,
                    presentation,
                    origin,
                    span: m.span,
                });
            }
            ShigureRealizationSpace::FiniteMembers(checked)
        }
        RawRealizationSpace::PolynomialScheme {
            equations,
            invertibles,
            is_raw_candidate,
            origin,
            ..
        } => {
            let eqs = check_named_polys_in_scope(
                equations,
                &coeff_domain,
                &u_set,
                &format!("{full_name}.realizations.equation"),
                control,
            )?;
            let invs = check_named_polys_in_scope(
                invertibles,
                &coeff_domain,
                &u_set,
                &format!("{full_name}.realizations.invertible"),
                control,
            )?;
            ShigureRealizationSpace::PolynomialScheme {
                equations: eqs,
                invertibles: invs,
                is_raw_candidate: *is_raw_candidate,
                origin: check_origin_ref(origin, &format!("{full_name}.realizations.scheme"))?,
            }
        }
    };

    let cand_space = match &raw.candidates.space {
        RawCandidateSpace::FiniteMembers { members, .. } => {
            let mut ids = HashSet::new();
            let mut checked = Vec::with_capacity(members.len());
            for m in members {
                E::checkpoint(control, Checkpoint::LawSemantics)?;
                if !ids.insert(m.id.name.clone()) {
                    return duplicate(
                        m.id.span,
                        format!(
                            "duplicate candidate member `{}` in `{full_name}`",
                            m.id.name
                        ),
                    );
                }
                let origin = check_origin_ref(&m.origin, &format!("{full_name}.{}", m.id.name))?;
                let assignments = check_member_assignments(
                    &m.assignments,
                    &c_vars,
                    &coeff_domain,
                    r_idx,
                    checker,
                    m.span,
                    &format!("{full_name}.{}", m.id.name),
                    control,
                )?;
                checked.push(ShigureCandidateMember {
                    id: m.id.name.clone(),
                    assignments,
                    origin,
                    span: m.span,
                });
            }
            ShigureCandidateSpace::FiniteMembers(checked)
        }
        RawCandidateSpace::PolynomialScheme {
            equations,
            invertibles,
            origin,
            ..
        } => {
            let eqs = check_named_polys_in_scope(
                equations,
                &coeff_domain,
                &c_set,
                &format!("{full_name}.candidates.equation"),
                control,
            )?;
            let invs = check_named_polys_in_scope(
                invertibles,
                &coeff_domain,
                &c_set,
                &format!("{full_name}.candidates.invertible"),
                control,
            )?;
            ShigureCandidateSpace::PolynomialScheme {
                equations: eqs,
                invertibles: invs,
                origin: check_origin_ref(origin, &format!("{full_name}.candidates.scheme"))?,
            }
        }
    };

    let goodness = check_goodness(
        &raw.goodness,
        &real_space,
        &coeff_domain,
        &u_owned,
        &b_owned,
        &c_owned,
        &full_name,
        r_idx,
        reading_name,
        checker,
        index,
        decls,
        edges,
        control,
    )?;

    let reading_comparison = raw
        .reading_comparison
        .as_ref()
        .map(|rc| {
            let empty_disjoint: [&HashSet<String>; 3] = [&u_owned, &b_owned, &c_owned];
            let fine_b_vars = collect_unique_vars::<E>(
                &rc.fine_b_vars,
                &format!("{full_name}.reading_comparison.fine_b_vars"),
                &empty_disjoint,
            )?;
            let fine_b_set: HashSet<&str> = fine_b_vars.iter().map(String::as_str).collect();
            if rc.fine_q.len() != fine_b_vars.len() {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    rc.span,
                    "`fine_q` length must match `fine_b_vars` length",
                ))
                .into());
            }
            for (i, expr) in rc.fine_q.iter().enumerate() {
                check_poly_literals::<E>(
                    expr,
                    LiteralDomainRule::Exact(&coeff_domain),
                    rc.span,
                    control,
                )?;
                check_poly_vars::<E>(
                    expr,
                    &u_set,
                    rc.span,
                    &format!("{full_name}.fine_q[{i}]"),
                    control,
                )?;
            }
            if rc.coarsen_r.len() != b_vars.len() {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    rc.span,
                    "`coarsen_r` length must match `b_vars` length",
                ))
                .into());
            }
            for (i, expr) in rc.coarsen_r.iter().enumerate() {
                check_poly_literals::<E>(
                    expr,
                    LiteralDomainRule::Exact(&coeff_domain),
                    rc.span,
                    control,
                )?;
                check_poly_vars::<E>(
                    expr,
                    &fine_b_set,
                    rc.span,
                    &format!("{full_name}.coarsen_r[{i}]"),
                    control,
                )?;
            }
            Ok::<_, E>(ShigureReadingComparison {
                name: rc.name.name.clone(),
                fine_b_vars,
                fine_q: rc.fine_q.clone(),
                coarsen_r: rc.coarsen_r.clone(),
                span: rc.span,
            })
        })
        .transpose()?;

    Ok(ShigureFamilySpec {
        name: full_name,
        reading: reading_name.to_owned(),
        coeff_domain,
        realizations: ShigureRealizationFamily {
            name: raw.realizations.name.name.clone(),
            u_vars,
            b_vars,
            reading_q: raw.realizations.reading_q.clone(),
            space: real_space,
            span: raw.realizations.span,
        },
        candidates: ShigureCandidateFamily {
            name: raw.candidates.name.name.clone(),
            c_vars,
            pi: raw.candidates.pi.clone(),
            space: cand_space,
            span: raw.candidates.span,
        },
        goodness,
        reading_comparison,
        span: raw.span,
    })
}

#[allow(clippy::too_many_arguments)]
fn check_goodness<E: InputError>(
    raw: &RawGoodnessSpec,
    real_space: &ShigureRealizationSpace,
    coeff_domain: &ShigureCoeffDomain,
    u_owned: &HashSet<String>,
    b_owned: &HashSet<String>,
    c_owned: &HashSet<String>,
    full_name: &str,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span, usize)>,
    decls: &CheckedShigureDecls,
    edges: &mut Vec<(usize, usize, Span)>,
    control: &Control,
) -> CResult<ShigureGoodnessSpec, E> {
    match raw {
        RawGoodnessSpec::Direct {
            equations,
            invertibles,
            preservation,
            raw_sequence,
            span,
        } => {
            let allowed: HashSet<&str> = u_owned.union(c_owned).map(String::as_str).collect();
            let eqs = check_named_polys_in_scope(
                equations,
                coeff_domain,
                &allowed,
                &format!("{full_name}.goodness.equation"),
                control,
            )?;
            let invs = check_named_polys_in_scope(
                invertibles,
                coeff_domain,
                &allowed,
                &format!("{full_name}.goodness.invertible"),
                control,
            )?;
            let pres = preservation
                .as_ref()
                .map(|p| {
                    check_preservation_source(
                        p,
                        coeff_domain,
                        &allowed,
                        full_name,
                        r_idx,
                        reading_name,
                        checker,
                        index,
                        decls,
                        edges,
                        control,
                    )
                })
                .transpose()?;
            let seq = raw_sequence
                .as_ref()
                .map(|s| {
                    check_raw_sequence(
                        s,
                        real_space,
                        coeff_domain,
                        decls,
                        *span,
                        full_name,
                        control,
                    )
                })
                .transpose()?;
            Ok(ShigureGoodnessSpec::Direct {
                equations: eqs,
                invertibles: invs,
                preservation: pres,
                raw_sequence: seq,
            })
        }
        RawGoodnessSpec::Existential {
            witness_vars,
            equations,
            invertibles,
            preservation,
            ..
        } => {
            let w_vars = collect_unique_vars(
                witness_vars,
                &format!("{full_name}.goodness.witness_vars"),
                &[u_owned, b_owned, c_owned],
            )?;
            let mut allowed: HashSet<&str> = u_owned.union(c_owned).map(String::as_str).collect();
            for w in &w_vars {
                allowed.insert(w.as_str());
            }
            let eqs = check_named_polys_in_scope(
                equations,
                coeff_domain,
                &allowed,
                &format!("{full_name}.goodness.equation"),
                control,
            )?;
            let invs = check_named_polys_in_scope(
                invertibles,
                coeff_domain,
                &allowed,
                &format!("{full_name}.goodness.invertible"),
                control,
            )?;
            let pres = preservation
                .as_ref()
                .map(|p| {
                    check_preservation_source(
                        p,
                        coeff_domain,
                        &allowed,
                        full_name,
                        r_idx,
                        reading_name,
                        checker,
                        index,
                        decls,
                        edges,
                        control,
                    )
                })
                .transpose()?;
            Ok(ShigureGoodnessSpec::Existential {
                witness_vars: w_vars,
                equations: eqs,
                invertibles: invs,
                preservation: pres,
            })
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn check_preservation_source<E: InputError>(
    raw: &RawPreservationSource,
    coeff_domain: &ShigureCoeffDomain,
    allowed_vars: &HashSet<&str>,
    full_name: &str,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span, usize)>,
    decls: &CheckedShigureDecls,
    edges: &mut Vec<(usize, usize, Span)>,
    control: &Control,
) -> CResult<ShigurePreservationSource, E> {
    let comparison = resolve_shigure_ref(
        &raw.comparison,
        DeclCategory::Comparison,
        r_idx,
        reading_name,
        checker,
        index,
        edges,
    )?;
    let change_spec = resolve_shigure_ref(
        &raw.change_spec,
        DeclCategory::ChangeSpec,
        r_idx,
        reading_name,
        checker,
        index,
        edges,
    )?;
    let cmp = &decls.comparisons[&comparison];
    let spec = &decls.change_specs[&change_spec];
    if &decls.presentations[&cmp.after].coeff_domain != coeff_domain
        || &spec.coeff_domain != coeff_domain
    {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw.span,
            format!("`preservation` comparison/change_spec coefficient domain must match family `{full_name}`"),
        ))
        .into());
    }
    super::check_relations::check_comparison_against_change_spec(
        cmp,
        &decls.presentations[&cmp.after],
        spec,
        control,
    )?;
    let spec_params: HashSet<&str> = spec.parameters.iter().map(|p| p.name.as_str()).collect();
    let mut param_bindings = BTreeMap::new();
    for (param, expr, span) in &raw.param_bindings {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !spec_params.contains(param.name.as_str()) {
            return reference(
                param.span,
                format!(
                    "unknown change_spec parameter `{}` in `{full_name}` preservation",
                    param.name
                ),
            );
        }
        if param_bindings.contains_key(&param.name) {
            return duplicate(
                param.span,
                format!(
                    "duplicate parameter binding `{}` in `{full_name}`",
                    param.name
                ),
            );
        }
        check_poly_literals(expr, LiteralDomainRule::Exact(coeff_domain), *span, control)?;
        check_poly_vars(
            expr,
            allowed_vars,
            *span,
            &format!("{full_name}.preservation.bind.{}", param.name),
            control,
        )?;
        param_bindings.insert(param.name.clone(), expr.clone());
    }
    for req in &spec.parameters {
        if !param_bindings.contains_key(&req.name) {
            return Err(Box::new(Issue::law(
                Code::Type,
                raw.span,
                format!(
                    "missing parameter binding for `{}` in `{full_name}` preservation",
                    req.name
                ),
            ))
            .into());
        }
    }
    Ok(ShigurePreservationSource {
        comparison,
        change_spec,
        param_bindings,
        span: raw.span,
    })
}

fn check_raw_sequence<E: InputError>(
    raw: &RawSequenceSpec,
    real_space: &ShigureRealizationSpace,
    coeff_domain: &ShigureCoeffDomain,
    decls: &CheckedShigureDecls,
    parent_span: Span,
    full_name: &str,
    control: &Control,
) -> CResult<ShigureRawSequenceSpec, E> {
    let ShigureRealizationSpace::FiniteMembers(members) = real_space else {
        return Err(Box::new(Issue::law(
            Code::Type,
            parent_span,
            "`raw_sequence` requires `realizations` to use finite `member` declarations",
        ))
        .into());
    };
    if raw.steps.is_empty() {
        return Err(Box::new(Issue::law(
            Code::Syntax,
            raw.span,
            "`raw_sequence` requires at least one `step`",
        ))
        .into());
    }
    if let Some(idx) = raw.baseline_step_index
        && idx >= raw.steps.len()
    {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw.span,
            format!(
                "`baseline_step_index` ({idx}) out of bounds (steps: {})",
                raw.steps.len()
            ),
        ))
        .into());
    }
    let mut start_state = BTreeMap::new();
    for (coord, lit, span) in &raw.start_state {
        if start_state.contains_key(&coord.name) {
            return duplicate(
                coord.span,
                format!("duplicate start_state `{}`", coord.name),
            );
        }
        check_scalar_lit(lit, coeff_domain, *span, control)?;
        start_state.insert(coord.name.clone(), lit.clone());
    }
    let mut steps = Vec::with_capacity(raw.steps.len());
    for st in &raw.steps {
        for arg in &st.args {
            check_scalar_lit(arg, coeff_domain, st.span, control)?;
        }
        steps.push((st.operation.name.clone(), st.args.clone()));
    }
    for m in members {
        if let Some(p_name) = &m.presentation {
            let pres = &decls.presentations[p_name];
            check_presentation_vars(pres, None, control)?;
            let Some(ph) = pres.phases.iter().find(|p| p.name == raw.start_phase.name) else {
                return reference(
                    raw.start_phase.span,
                    format!(
                        "unknown phase `{}` in presentation `{p_name}`",
                        raw.start_phase.name
                    ),
                );
            };
            let ph_coords: HashSet<&str> = ph.coords.iter().map(|c| c.name.as_str()).collect();
            for k in start_state.keys() {
                if !ph_coords.contains(k.as_str()) {
                    return reference(
                        raw.span,
                        format!(
                            "unknown start_state coordinate `{k}` for `{p_name}.{}` in `{full_name}`",
                            ph.name
                        ),
                    );
                }
            }
            for (op_name, args) in &steps {
                let Some(op) = pres.operations.iter().find(|o| &o.name == op_name) else {
                    return reference(
                        raw.span,
                        format!("unknown step operation `{op_name}` in `{p_name}`"),
                    );
                };
                if op.args.len() != args.len() {
                    return Err(Box::new(Issue::law(
                        Code::Type,
                        raw.span,
                        format!(
                            "step operation `{op_name}` expects {} args, got {}",
                            op.args.len(),
                            args.len()
                        ),
                    ))
                    .into());
                }
            }
            if !pres
                .observations
                .iter()
                .any(|o| o.name == raw.observation_name.name)
            {
                return reference(
                    raw.observation_name.span,
                    format!(
                        "unknown observation `{}` in `{p_name}`",
                        raw.observation_name.name
                    ),
                );
            }
        }
    }
    Ok(ShigureRawSequenceSpec {
        start_phase: raw.start_phase.name.clone(),
        start_state,
        steps,
        observation_name: raw.observation_name.name.clone(),
        baseline_step_index: raw.baseline_step_index,
        span: raw.span,
    })
}
