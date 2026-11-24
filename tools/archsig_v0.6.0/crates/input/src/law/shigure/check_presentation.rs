//! `shigure presentation` の静的検査と原始観測 field 解決。

use super::check::{CResult, LiteralDomainRule, check_coeff_domain, check_poly_literals};
use super::*;
use crate::definition::CheckedDefinitions;
use crate::law::ast::{QName, Span};
use crate::law::check::{Checker, duplicate, full, reference, syntax};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::issue::{Code, Details, Issue, Location};
use archsig_common::json::InputError;
use archsig_common::types::Type;
use std::collections::{BTreeSet, HashMap, HashSet};

pub(super) fn check_presentation<E: InputError>(
    raw: &RawPresentation,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    control: &Control,
) -> CResult<ShigurePresentation, E> {
    let full_name = full(reading_name, &[&raw.name.name]);
    let coeff_domain = check_coeff_domain(&raw.domain, control)?;

    let mut sort_names = HashSet::new();
    let mut sorts = Vec::with_capacity(raw.sorts.len());
    for s in &raw.sorts {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if s.rank == 0 {
            return Err(Box::new(Issue::law(
                Code::Type,
                s.span,
                format!("sort `{}` must have rank >= 1", s.name.name),
            ))
            .into());
        }
        if !sort_names.insert(s.name.name.clone()) {
            return duplicate(s.name.span, format!("duplicate sort `{}`", s.name.name));
        }
        sorts.push(ShigureSortDecl {
            name: s.name.name.clone(),
            rank: s.rank,
            span: s.span,
        });
    }

    let mut phase_coords: HashMap<String, HashSet<String>> = HashMap::new();
    let mut phases = Vec::with_capacity(raw.phases.len());
    for ph in &raw.phases {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if phase_coords.contains_key(&ph.name.name) {
            return duplicate(ph.name.span, format!("duplicate phase `{}`", ph.name.name));
        }
        let mut coords = Vec::with_capacity(ph.coords.len());
        let mut coord_names = HashSet::new();
        for c in &ph.coords {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            if !coord_names.insert(c.name.name.clone()) {
                return duplicate(
                    c.name.span,
                    format!(
                        "duplicate coordinate `{}` in phase `{}`",
                        c.name.name, ph.name.name
                    ),
                );
            }
            if !sort_names.contains(&c.sort.name) {
                return reference(
                    c.sort.span,
                    format!(
                        "unknown sort `{}` in coordinate `{}`",
                        c.sort.name, c.name.name
                    ),
                );
            }
            let binding = match &c.binding {
                RawCoordBinding::Symbolic => ShigureCoordBinding::Symbolic,
                RawCoordBinding::ObservedField { field, span } => resolve_observed_field(
                    field,
                    *span,
                    &coeff_domain,
                    &checker.imports[r_idx],
                    checker.definitions,
                )?,
            };
            coords.push(ShigureCoordDecl {
                name: c.name.name.clone(),
                sort: c.sort.name.clone(),
                binding,
                span: c.span,
            });
        }
        let mut law_names = HashSet::new();
        let mut state_laws = Vec::with_capacity(ph.state_laws.len());
        for l in &ph.state_laws {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            if !law_names.insert(l.name.name.clone()) {
                return duplicate(
                    l.name.span,
                    format!(
                        "duplicate state law `{}` in phase `{}`",
                        l.name.name, ph.name.name
                    ),
                );
            }
            check_poly_literals(
                &l.expr,
                LiteralDomainRule::Exact(&coeff_domain),
                l.span,
                control,
            )?;
            state_laws.push(ShigureStateLawDecl {
                name: l.name.name.clone(),
                kind: l.kind,
                expr: l.expr.clone(),
                span: l.span,
            });
        }
        phase_coords.insert(ph.name.name.clone(), coord_names);
        phases.push(ShigurePhaseDecl {
            name: ph.name.name.clone(),
            coords,
            state_laws,
            span: ph.span,
        });
    }

    let mut op_names = HashSet::new();
    let mut operations = Vec::with_capacity(raw.operations.len());
    for op in &raw.operations {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !op_names.insert(op.name.name.clone()) {
            return duplicate(
                op.name.span,
                format!("duplicate operation `{}`", op.name.name),
            );
        }
        let Some(source_coords) = phase_coords.get(&op.source_phase.name) else {
            return reference(
                op.source_phase.span,
                format!("unknown source phase `{}`", op.source_phase.name),
            );
        };
        let Some(target_coords) = phase_coords.get(&op.target_phase.name) else {
            return reference(
                op.target_phase.span,
                format!("unknown target phase `{}`", op.target_phase.name),
            );
        };
        let mut arg_names = HashSet::new();
        let mut args = Vec::with_capacity(op.args.len());
        for (a_name, a_sort) in &op.args {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            if !arg_names.insert(a_name.name.clone()) {
                return duplicate(a_name.span, format!("duplicate argument `{}`", a_name.name));
            }
            if source_coords.contains(&a_name.name) {
                return duplicate(
                    a_name.span,
                    format!(
                        "argument `{}` of operation `{}` collides with coordinate of source phase `{}`",
                        a_name.name, op.name.name, op.source_phase.name
                    ),
                );
            }
            if !sort_names.contains(&a_sort.name) {
                return reference(
                    a_sort.span,
                    format!(
                        "unknown sort `{}` in argument `{}`",
                        a_sort.name, a_name.name
                    ),
                );
            }
            args.push((a_name.name.clone(), a_sort.name.clone()));
        }
        let mut seen_updates = HashSet::new();
        let mut updates = Vec::with_capacity(op.updates.len());
        for (u_name, u_expr) in &op.updates {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            if !target_coords.contains(&u_name.name) {
                return reference(
                    u_name.span,
                    format!(
                        "update targets unknown coordinate `{}` of phase `{}`",
                        u_name.name, op.target_phase.name
                    ),
                );
            }
            if !seen_updates.insert(u_name.name.clone()) {
                return duplicate(
                    u_name.span,
                    format!("duplicate update for coordinate `{}`", u_name.name),
                );
            }
            check_poly_literals(
                u_expr,
                LiteralDomainRule::Exact(&coeff_domain),
                op.span,
                control,
            )?;
            updates.push((u_name.name.clone(), u_expr.clone()));
        }
        if seen_updates.len() != target_coords.len() {
            return Err(Box::new(Issue::law(
                Code::Type,
                op.span,
                format!(
                    "operation `{}` must assign every coordinate of target phase `{}`",
                    op.name.name, op.target_phase.name
                ),
            ))
            .into());
        }
        let domain_laws = super::check_ext_common::check_state_law_list(
            &op.domain_laws,
            &coeff_domain,
            &format!("operation `{}`", op.name.name),
            control,
        )?;
        operations.push(ShigureOperationDecl {
            name: op.name.name.clone(),
            source_phase: op.source_phase.name.clone(),
            target_phase: op.target_phase.name.clone(),
            args,
            domain_laws,
            updates,
            span: op.span,
        });
    }

    let mut obs_keys = HashSet::new();
    let mut observations = Vec::with_capacity(raw.observations.len());
    for obs in &raw.observations {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !phase_coords.contains_key(&obs.phase.name) {
            return reference(
                obs.phase.span,
                format!(
                    "unknown phase `{}` in observation `{}`",
                    obs.phase.name, obs.name.name
                ),
            );
        }
        if !obs_keys.insert((obs.phase.name.clone(), obs.name.name.clone())) {
            return duplicate(
                obs.name.span,
                format!(
                    "duplicate observation `{}` on phase `{}`",
                    obs.name.name, obs.phase.name
                ),
            );
        }
        if obs.components.is_empty() {
            return syntax(
                obs.span,
                format!(
                    "observation `{}` must have at least one component",
                    obs.name.name
                ),
            );
        }
        for comp in &obs.components {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            check_poly_literals(
                comp,
                LiteralDomainRule::Exact(&coeff_domain),
                obs.span,
                control,
            )?;
        }
        observations.push(ShigureObservationDecl {
            name: obs.name.name.clone(),
            phase: obs.phase.name.clone(),
            components: obs.components.clone(),
            span: obs.span,
        });
    }

    Ok(ShigurePresentation {
        name: full_name,
        reading: reading_name.to_owned(),
        coeff_domain,
        sorts,
        phases,
        operations,
        observations,
        span: raw.span,
    })
}

pub(super) fn resolve_observed_field<E: InputError>(
    qname: &QName,
    span: Span,
    domain: &ShigureCoeffDomain,
    imported_vocabs: &BTreeSet<String>,
    definitions: &CheckedDefinitions,
) -> CResult<ShigureCoordBinding, E> {
    let parts: Vec<&str> = qname.parts.iter().map(|p| p.name.as_str()).collect();
    let (entity_full, field_short) = match parts.as_slice() {
        [entity, field] => {
            let mut matches = Vec::new();
            for ns in imported_vocabs {
                let candidate = format!("{ns}.{entity}");
                if definitions.declarations.contains_key(&candidate) {
                    matches.push(candidate);
                }
            }
            if matches.is_empty() {
                return reference(
                    span,
                    format!("unknown primitive entity `{entity}` in imported vocabularies"),
                );
            }
            if matches.len() > 1 {
                return reference(
                    span,
                    format!(
                        "ambiguous entity `{entity}` across imported vocabularies; use qualified name"
                    ),
                );
            }
            (matches.remove(0), *field)
        }
        [ns, entity, field] => {
            if !imported_vocabs.contains(*ns) {
                return reference(
                    span,
                    format!("vocabulary `{ns}` is not imported in this reading"),
                );
            }
            let candidate = format!("{ns}.{entity}");
            if !definitions.declarations.contains_key(&candidate) {
                return reference(span, format!("unknown primitive declaration `{candidate}`"));
            }
            (candidate, *field)
        }
        _ => {
            return syntax(
                span,
                "observed field binding must be `Entity.field` or `Namespace.Entity.field`",
            );
        }
    };

    let decl = &definitions.declarations[&entity_full];
    let Some((params, fields)) = decl.signature.record_fields() else {
        return Err(Box::new(Issue::law(
            Code::Type,
            span,
            format!("`{entity_full}` is not an entity/arrow/correspondence with fields"),
        ))
        .into());
    };
    let Some(field_def) = params.iter().chain(fields).find(|f| f.name == field_short) else {
        return reference(
            span,
            format!("unknown field `{field_short}` on `{entity_full}`"),
        );
    };
    let expected_ty = match domain {
        ShigureCoeffDomain::Z => Type::Z,
        ShigureCoeffDomain::Q => Type::Q,
        ShigureCoeffDomain::Fp(p) => Type::Fp(p.to_string()),
    };
    if field_def.ty != expected_ty {
        return Err(Box::new(Issue {
            code: Code::Type,
            message: format!(
                "observed field `{entity_full}.{field_short}` type does not match presentation coefficient domain"
            ),
            location: Location::Law { span },
            details: Details::Type {
                expected: expected_ty,
                actual: field_def.ty.clone(),
            },
        })
        .into());
    }
    Ok(ShigureCoordBinding::ObservedField {
        entity: entity_full.clone(),
        field: format!("{entity_full}.{field_short}"),
        span,
    })
}
