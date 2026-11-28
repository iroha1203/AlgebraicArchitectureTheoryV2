//! Phase 5 静的意味検査の共通ヘルパ（記号 `observed` 参照・座標・制約検査）。

use super::ShigureCoeffDomain;
use super::ast_ext::ShigureScalarLit;
use super::ast_phase3::{RawMemberCoordValue, ShigureMemberCoordValue};
use super::ast_phase5_obs::{RawSymbolicValue, ShigureSymbolicValue};
use super::ast_phase5_rev::{
    RawRevisionConstraint, RawRevisionCoord, RawRevisionPredicate, ShigureRevisionConstraint,
    ShigureRevisionCoord, ShigureRevisionPredicate,
};
use super::check::{CResult, CoordCheckCtx, check_member_coord_value};
use super::check_ext_common::check_scalar_lit;
use super::check_phase4_lift_artin::p4_type_err;
use crate::law::ast::{QName, Span};
use crate::law::check::{Checker, duplicate, reference, syntax};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;
use archsig_common::types::Type;
use num_bigint::BigInt;
use num_traits::Signed;
use std::collections::HashSet;

pub(super) fn resolve_symbolic_observed_field<E: InputError>(
    qname: &QName,
    span: Span,
    r_idx: usize,
    checker: &Checker<'_, E>,
) -> CResult<(String, String), E> {
    let imported_vocabs = &checker.imports[r_idx];
    let definitions = checker.definitions;
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
    if !matches!(
        field_def.ty,
        Type::Z | Type::Q | Type::Fp(_) | Type::Text | Type::Bool
    ) {
        return p4_type_err(
            span,
            format!(
                "observed field `{entity_full}.{field_short}` must have scalar, text, or bool type"
            ),
        );
    }
    Ok((entity_full.clone(), format!("{entity_full}.{field_short}")))
}

pub(super) fn check_symbolic_value<E: InputError>(
    raw: &RawSymbolicValue,
    r_idx: usize,
    checker: &Checker<'_, E>,
    context: &str,
) -> CResult<ShigureSymbolicValue, E> {
    match raw {
        RawSymbolicValue::Literal(s, span) => {
            if s.trim().is_empty() {
                return p4_type_err(
                    *span,
                    format!("symbol literal must be non-empty in {context}"),
                );
            }
            Ok(ShigureSymbolicValue::Literal(s.clone()))
        }
        RawSymbolicValue::ObservedField { field, span } => {
            let (entity, field_full) =
                resolve_symbolic_observed_field(field, *span, r_idx, checker)?;
            Ok(ShigureSymbolicValue::ObservedField {
                entity,
                field: field_full,
                span: *span,
            })
        }
        RawSymbolicValue::Missing(_) => Ok(ShigureSymbolicValue::Missing),
    }
}

pub(super) fn check_p5_revision_coords<E: InputError>(
    raw_coords: &[RawRevisionCoord],
    coeff_domain: &ShigureCoeffDomain,
    control: &Control,
    context: &str,
) -> CResult<(Vec<ShigureRevisionCoord>, HashSet<String>), E> {
    let mut seen = HashSet::new();
    let mut out = Vec::with_capacity(raw_coords.len());
    for c in raw_coords {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !seen.insert(c.id.name.clone()) {
            return duplicate(
                c.id.span,
                format!("duplicate coord `{}` in {context}", c.id.name),
            );
        }
        if c.domain_values.is_empty() {
            return p4_type_err(
                c.span,
                format!("coord `{}` has empty domain_values in {context}", c.id.name),
            );
        }
        for v in &c.domain_values {
            check_scalar_lit(v, coeff_domain, c.span, control)?;
        }
        out.push(ShigureRevisionCoord {
            id: c.id.name.clone(),
            domain_values: c.domain_values.clone(),
            span: c.span,
        });
    }
    Ok((out, seen))
}

pub(super) fn check_p5_revision_constraints<E: InputError>(
    raw: &[RawRevisionConstraint],
    coord_names: &HashSet<String>,
    coeff_domain: &ShigureCoeffDomain,
    control: &Control,
    context: &str,
) -> CResult<Vec<ShigureRevisionConstraint>, E> {
    let mut out = Vec::with_capacity(raw.len());
    for con in raw {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        let mut sup = HashSet::new();
        let mut support = Vec::with_capacity(con.support.len());
        for s in &con.support {
            if !coord_names.contains(&s.name) {
                return reference(
                    s.span,
                    format!(
                        "unknown coord `{}` in constraint `{}` support ({context})",
                        s.name, con.id.name
                    ),
                );
            }
            sup.insert(s.name.as_str());
            support.push(s.name.clone());
        }
        let predicate = match &con.predicate {
            RawRevisionPredicate::Equality(a, b) => {
                for x in [a, b] {
                    if !coord_names.contains(&x.name) {
                        return reference(
                            x.span,
                            format!("unknown coord `{}` in constraint `{}`", x.name, con.id.name),
                        );
                    }
                    if !sup.contains(x.name.as_str()) {
                        return p4_type_err(
                            x.span,
                            format!(
                                "constraint `{}` support must include `{}`",
                                con.id.name, x.name
                            ),
                        );
                    }
                }
                ShigureRevisionPredicate::Equality(a.name.clone(), b.name.clone())
            }
            RawRevisionPredicate::LinearZero { terms } => {
                let mut checked_terms = Vec::with_capacity(terms.len());
                for (coeff, x) in terms {
                    check_scalar_lit(coeff, coeff_domain, con.span, control)?;
                    if !coord_names.contains(&x.name) {
                        return reference(
                            x.span,
                            format!("unknown coord `{}` in constraint `{}`", x.name, con.id.name),
                        );
                    }
                    if !sup.contains(x.name.as_str()) {
                        return p4_type_err(
                            x.span,
                            format!(
                                "constraint `{}` support must include `{}`",
                                con.id.name, x.name
                            ),
                        );
                    }
                    checked_terms.push((coeff.clone(), x.name.clone()));
                }
                ShigureRevisionPredicate::LinearZero {
                    terms: checked_terms,
                }
            }
            RawRevisionPredicate::AllowedTuples { coords, tuples } => {
                let mut checked_coords = Vec::with_capacity(coords.len());
                for x in coords {
                    if !coord_names.contains(&x.name) {
                        return reference(
                            x.span,
                            format!("unknown coord `{}` in constraint `{}`", x.name, con.id.name),
                        );
                    }
                    if !sup.contains(x.name.as_str()) {
                        return p4_type_err(
                            x.span,
                            format!(
                                "constraint `{}` support must include `{}`",
                                con.id.name, x.name
                            ),
                        );
                    }
                    checked_coords.push(x.name.clone());
                }
                for tup in tuples {
                    if tup.len() != checked_coords.len() {
                        return p4_type_err(
                            con.span,
                            format!(
                                "allowed_tuples tuple length {} does not match coords length {} in `{}`",
                                tup.len(),
                                checked_coords.len(),
                                con.id.name
                            ),
                        );
                    }
                    for v in tup {
                        check_scalar_lit(v, coeff_domain, con.span, control)?;
                    }
                }
                ShigureRevisionPredicate::AllowedTuples {
                    coords: checked_coords,
                    tuples: tuples.clone(),
                }
            }
        };
        out.push(ShigureRevisionConstraint {
            id: con.id.name.clone(),
            support,
            predicate,
            span: con.span,
        });
    }
    Ok(out)
}

pub(super) fn check_p5_coord_assignments<E: InputError>(
    raw: &[(crate::law::ast::Ident, RawMemberCoordValue, Span)],
    coord_names: &HashSet<String>,
    coord_ctx: &CoordCheckCtx<'_, '_, E>,
    context: &str,
) -> CResult<Vec<(String, ShigureMemberCoordValue)>, E> {
    let mut seen = HashSet::new();
    let mut out = Vec::with_capacity(raw.len());
    for (c, val, span) in raw {
        E::checkpoint(coord_ctx.control, Checkpoint::LawSemantics)?;
        if !coord_names.contains(&c.name) {
            return reference(c.span, format!("unknown coord `{}` in {context}", c.name));
        }
        if !seen.insert(c.name.as_str()) {
            return duplicate(
                c.span,
                format!("duplicate assignment to coord `{}` in {context}", c.name),
            );
        }
        let checked_val = check_member_coord_value(val, coord_ctx, *span)?;
        out.push((c.name.clone(), checked_val));
    }
    Ok(out)
}

pub(super) fn check_nonnegative_cost_lit<E: InputError>(
    lit: &ShigureScalarLit,
    span: Span,
    context: &str,
) -> CResult<(), E> {
    match lit {
        ShigureScalarLit::Int(n) => {
            if n.is_negative() {
                return p4_type_err(span, format!("{context} cost must be nonnegative"));
            }
            Ok(())
        }
        ShigureScalarLit::Rat { num, den } => {
            if *den <= BigInt::from(0) || num.is_negative() {
                return p4_type_err(span, format!("{context} cost must be nonnegative rational"));
            }
            Ok(())
        }
        ShigureScalarLit::Fp { .. } => p4_type_err(
            span,
            format!("{context} cost cannot be finite-field literal"),
        ),
    }
}
