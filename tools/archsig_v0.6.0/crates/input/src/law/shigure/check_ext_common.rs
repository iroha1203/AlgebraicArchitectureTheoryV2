//! 拡張 SHIGURE 宣言向けの共通静的検査ヘルパ。
//!
//! 射本体検査は `check_ext_morphism`、スコープ付き `change_spec` 検査は `check_ext_scope` へ分割している。

use super::check::{CResult, LiteralDomainRule, check_poly_literals, check_poly_vars};
use super::*;
use crate::law::ast::Span;
use crate::law::check::duplicate;
use archsig_common::control::{Checkpoint, Control};
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;
use archsig_common::prime::is_prime_controlled;
use num_bigint::BigInt;
use num_traits::Zero;
use std::collections::HashSet;

pub(super) use super::check_ext_morphism::{check_morphism_body, check_morphism_vars_against_pres};
pub(super) use super::check_ext_scope::{ScopedMorphismMeta, check_scoped_change_spec_targets};

pub(super) fn check_scalar_lit<E: InputError>(
    lit: &ShigureScalarLit,
    domain: &ShigureCoeffDomain,
    span: Span,
    control: &Control,
) -> CResult<(), E> {
    match (lit, domain) {
        (ShigureScalarLit::Int(_), ShigureCoeffDomain::Z | ShigureCoeffDomain::Q) => Ok(()),
        (ShigureScalarLit::Int(n), ShigureCoeffDomain::Fp(p)) => {
            if n.to_biguint().is_some_and(|u| &u < p) {
                Ok(())
            } else {
                Err(Box::new(Issue::law(
                    Code::Type,
                    span,
                    format!("integer literal `{n}` in Fp({p}) must satisfy 0 <= value < {p}"),
                ))
                .into())
            }
        }
        (ShigureScalarLit::Rat { den, .. }, ShigureCoeffDomain::Q) => {
            if *den <= BigInt::zero() {
                Err(Box::new(Issue::law(
                    Code::Type,
                    span,
                    "rational denominator must be positive",
                ))
                .into())
            } else {
                Ok(())
            }
        }
        (ShigureScalarLit::Rat { .. }, _) => Err(Box::new(Issue::law(
            Code::Type,
            span,
            "rational literal `rat(n,d)` is only valid in coefficient domain Q",
        ))
        .into()),
        (ShigureScalarLit::Fp { value, modulus }, ShigureCoeffDomain::Fp(expected)) => {
            if !is_prime_controlled::<E>(modulus, control, Checkpoint::LawSemantics)? {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    span,
                    format!("Fp literal modulus `{modulus}` must be prime"),
                ))
                .into());
            }
            if modulus != expected {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    span,
                    "Fp literal modulus does not match declaration coefficient domain",
                ))
                .into());
            }
            if value >= modulus {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    span,
                    format!("Fp literal `{value}` must satisfy 0 <= value < {modulus}"),
                ))
                .into());
            }
            Ok(())
        }
        (ShigureScalarLit::Fp { .. }, _) => Err(Box::new(Issue::law(
            Code::Type,
            span,
            "Fp literal is incompatible with coefficient domain",
        ))
        .into()),
    }
}

pub(super) fn check_state_law_list<E: InputError>(
    raw_laws: &[RawStateLawDecl],
    coeff_domain: &ShigureCoeffDomain,
    dup_context: &str,
    control: &Control,
) -> CResult<Vec<ShigureStateLawDecl>, E> {
    let mut seen = HashSet::new();
    let mut out = Vec::with_capacity(raw_laws.len());
    for l in raw_laws {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !seen.insert(l.name.name.clone()) {
            return duplicate(
                l.name.span,
                format!("duplicate state law `{}` in {dup_context}", l.name.name),
            );
        }
        check_poly_literals(
            &l.expr,
            LiteralDomainRule::Exact(coeff_domain),
            l.span,
            control,
        )?;
        out.push(ShigureStateLawDecl {
            name: l.name.name.clone(),
            kind: l.kind,
            expr: l.expr.clone(),
            span: l.span,
        });
    }
    Ok(out)
}

pub(super) fn check_eval_cond_against_domain_params<E: InputError>(
    ec: &ShigureEvalCondition,
    coeff_domain: &ShigureCoeffDomain,
    param_set: &HashSet<&str>,
    span: Span,
    control: &Control,
) -> CResult<(), E> {
    let compatible = match (coeff_domain, &ec.point_domain) {
        (ShigureCoeffDomain::Q, ShigurePointDomain::AlgebraicClosure)
        | (ShigureCoeffDomain::Q, ShigurePointDomain::RationalPoints)
        | (ShigureCoeffDomain::Q, ShigurePointDomain::UniversalRing)
        | (ShigureCoeffDomain::Z, ShigurePointDomain::AlgebraicClosure)
        | (ShigureCoeffDomain::Z, ShigurePointDomain::RationalPoints)
        | (ShigureCoeffDomain::Z, ShigurePointDomain::IntegerPoints)
        | (ShigureCoeffDomain::Z, ShigurePointDomain::UniversalRing) => true,
        (ShigureCoeffDomain::Fp(p1), ShigurePointDomain::FiniteFieldPoints(p2)) => p1 == p2,
        (ShigureCoeffDomain::Fp(_), ShigurePointDomain::UniversalRing) => true,
        _ => false,
    };
    if !compatible {
        return Err(Box::new(Issue::law(
            Code::Type,
            span,
            "`eval_condition` point_domain is incompatible with `change_spec` coefficient domain",
        ))
        .into());
    }
    for item in ec
        .evaluations
        .iter()
        .chain(&ec.equations)
        .chain(&ec.invertibles)
    {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        check_poly_literals(
            &item.expr,
            LiteralDomainRule::Exact(coeff_domain),
            item.span,
            control,
        )?;
        let ctx = format!("{}.{}", ec.name, item.name);
        check_poly_vars(&item.expr, param_set, item.span, &ctx, control)?;
    }
    Ok(())
}

pub(super) fn check_coords_disjoint_from_params<E: InputError>(
    coords: &[ShigureCoordDecl],
    params: &HashSet<&str>,
    pres_name: &str,
    phase_name: &str,
    context: &str,
    control: &Control,
) -> CResult<(), E> {
    for c in coords {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if params.contains(c.name.as_str()) {
            return duplicate(
                c.span,
                format!(
                    "coordinate `{}` in `{pres_name}.{phase_name}` collides with change_spec parameter in {context}",
                    c.name
                ),
            );
        }
    }
    Ok(())
}
