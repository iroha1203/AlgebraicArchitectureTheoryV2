//! `ComparisonPair`・`ChangeSpec`・`EvalCondition` の検証。

use crate::ir::change::{
    ChangeSpec, EditableTarget, EvalCondition, FixedTarget, NamedPoly, PointDomain,
};
use crate::ir::presentation::{ComparisonPair, LawKind, Presentation};
use crate::ir::term::CoeffDomain;
use crate::ir::validate::{
    CheckedChangeSpec, CheckedComparisonPair, CheckedEvalCondition, ValidationError,
    require_non_empty, validate_allowed_params, validate_coeff_domain, validate_opt_source_ref,
    validate_poly_expr, validate_presentation_checked_params, validate_provenance,
};
use archsig_common::prime::is_prime;
use std::collections::{BTreeMap, BTreeSet};

/// 変更前後の `ComparisonPair`（`before`, `after`, `h`, `tau`）を検証する。
pub fn validate_comparison_pair(
    pair: ComparisonPair,
    allowed_params: &BTreeSet<String>,
) -> Result<CheckedComparisonPair, ValidationError> {
    validate_allowed_params(allowed_params, "comparison_pair.allowed_params")?;
    validate_comparison_pair_checked_params(pair, allowed_params)
}

pub(crate) fn validate_comparison_pair_checked_params(
    pair: ComparisonPair,
    allowed_params: &BTreeSet<String>,
) -> Result<CheckedComparisonPair, ValidationError> {
    if pair.before.name == pair.after.name {
        return Err(ValidationError::DuplicateDecl {
            kind: "presentation",
            name: pair.before.name.clone(),
        });
    }
    if pair.before.coeff_domain != pair.after.coeff_domain {
        return Err(ValidationError::DomainMismatch {
            expected: pair.before.coeff_domain.clone(),
            actual: pair.after.coeff_domain.clone(),
            context: "comparison pair before/after".to_owned(),
        });
    }
    let before = validate_presentation_checked_params(pair.before, allowed_params)?;
    let after = validate_presentation_checked_params(pair.after, allowed_params)?;
    let domain = &before.inner().coeff_domain;

    let before_phase_coords: BTreeMap<&str, BTreeSet<String>> = before
        .inner()
        .phases
        .iter()
        .map(|p| {
            (
                p.name.as_str(),
                p.coords.iter().map(|c| c.name.clone()).collect(),
            )
        })
        .collect();
    let after_phase_coords: BTreeMap<&str, BTreeSet<String>> = after
        .inner()
        .phases
        .iter()
        .map(|p| {
            (
                p.name.as_str(),
                p.coords.iter().map(|c| c.name.clone()).collect(),
            )
        })
        .collect();

    let mut h_by_after_phase: BTreeMap<String, String> = BTreeMap::new();
    let empty_args = BTreeSet::new();
    for sc in &pair.state_comparisons {
        validate_opt_source_ref(
            sc.provenance.as_ref(),
            &format!("state_comparison `{}`", sc.after_phase),
        )?;
        let Some(after_coords) = after_phase_coords.get(sc.after_phase.as_str()) else {
            return Err(ValidationError::UnknownRef {
                kind: "after phase",
                name: sc.after_phase.clone(),
                context: "state_comparison".to_owned(),
            });
        };
        let Some(before_coords) = before_phase_coords.get(sc.before_phase.as_str()) else {
            return Err(ValidationError::UnknownRef {
                kind: "before phase",
                name: sc.before_phase.clone(),
                context: format!("state_comparison `{}`", sc.after_phase),
            });
        };
        if h_by_after_phase
            .insert(sc.after_phase.clone(), sc.before_phase.clone())
            .is_some()
        {
            return Err(ValidationError::DuplicateDecl {
                kind: "state_comparison",
                name: sc.after_phase.clone(),
            });
        }
        for bc in before_coords {
            if !sc.map.contains_key(bc) {
                return Err(ValidationError::MissingCoordUpdate {
                    operation: format!("state_comparison({})", sc.after_phase),
                    coord: bc.clone(),
                });
            }
        }
        for (coord, expr) in &sc.map {
            if !before_coords.contains(coord) {
                return Err(ValidationError::UnknownCoordUpdate {
                    operation: format!("state_comparison({})", sc.after_phase),
                    coord: coord.clone(),
                });
            }
            validate_poly_expr(
                expr,
                domain,
                after_coords,
                &empty_args,
                allowed_params,
                &format!("state_comparison `{}.{coord}`", sc.after_phase),
            )?;
        }
    }
    for phase in &after.inner().phases {
        if !h_by_after_phase.contains_key(&phase.name) {
            return Err(ValidationError::MissingStateComparison {
                after_phase: phase.name.clone(),
            });
        }
    }

    // 各状態比較 h: after_phase -> before_phase について、before_phase 上の全観測が
    // after_phase 上に同名・同成分数で存在することを事前索引で O(O log O + P) 検証する。
    let mut before_obs_by_phase: BTreeMap<&str, Vec<(&str, usize)>> = BTreeMap::new();
    for obs in &before.inner().observations {
        before_obs_by_phase
            .entry(obs.phase.as_str())
            .or_default()
            .push((obs.name.as_str(), obs.components.len()));
    }
    let after_obs_arities: BTreeMap<(&str, &str), usize> = after
        .inner()
        .observations
        .iter()
        .map(|obs| {
            (
                (obs.phase.as_str(), obs.name.as_str()),
                obs.components.len(),
            )
        })
        .collect();
    for (after_phase_name, before_phase_name) in &h_by_after_phase {
        if let Some(before_list) = before_obs_by_phase.get(before_phase_name.as_str()) {
            for &(obs_name, expected_arity) in before_list {
                let Some(&actual_arity) =
                    after_obs_arities.get(&(after_phase_name.as_str(), obs_name))
                else {
                    return Err(ValidationError::MissingObservation {
                        after_phase: after_phase_name.clone(),
                        before_phase: before_phase_name.clone(),
                        observation: obs_name.to_owned(),
                    });
                };
                if actual_arity != expected_arity {
                    return Err(ValidationError::ArityMismatch {
                        context: format!(
                            "observation `{obs_name}` between after phase `{after_phase_name}` and before phase `{before_phase_name}`"
                        ),
                        expected: expected_arity,
                        actual: actual_arity,
                    });
                }
            }
        }
    }

    let before_ops: BTreeMap<&str, _> = before
        .inner()
        .operations
        .iter()
        .map(|op| (op.name.as_str(), op))
        .collect();
    let after_ops: BTreeMap<&str, _> = after
        .inner()
        .operations
        .iter()
        .map(|op| (op.name.as_str(), op))
        .collect();

    let mut seen_ops = BTreeSet::new();
    for tw in &pair.word_translation.entries {
        validate_opt_source_ref(
            tw.provenance.as_ref(),
            &format!("word_translation `{}`", tw.after_operation),
        )?;
        let Some(&after_op) = after_ops.get(tw.after_operation.as_str()) else {
            return Err(ValidationError::UnknownRef {
                kind: "after operation",
                name: tw.after_operation.clone(),
                context: "word_translation".to_owned(),
            });
        };
        if !seen_ops.insert(tw.after_operation.clone()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "word_translation",
                name: tw.after_operation.clone(),
            });
        }
        let expected_start = &h_by_after_phase[&after_op.source_phase];
        let expected_end = &h_by_after_phase[&after_op.target_phase];
        let after_src_coords = &after_phase_coords[after_op.source_phase.as_str()];
        let after_args: BTreeSet<String> =
            after_op.args.iter().map(|(name, _)| name.clone()).collect();

        if tw.steps.is_empty() {
            if expected_start != expected_end {
                return Err(ValidationError::PhasePathMismatch {
                    after_operation: tw.after_operation.clone(),
                    detail: format!(
                        "empty word requires same before phase, got `{expected_start}` -> `{expected_end}`"
                    ),
                });
            }
        } else {
            let mut current_phase = expected_start.as_str();
            for (idx, step) in tw.steps.iter().enumerate() {
                let Some(&before_op) = before_ops.get(step.before_operation.as_str()) else {
                    return Err(ValidationError::UnknownRef {
                        kind: "before operation",
                        name: step.before_operation.clone(),
                        context: format!("word_translation `{}` step {idx}", tw.after_operation),
                    });
                };
                if before_op.source_phase != current_phase {
                    return Err(ValidationError::PhasePathMismatch {
                        after_operation: tw.after_operation.clone(),
                        detail: format!(
                            "step {idx} (`{}`) expects source phase `{current_phase}`, got `{}`",
                            before_op.name, before_op.source_phase
                        ),
                    });
                }
                if step.arg_exprs.len() != before_op.args.len() {
                    return Err(ValidationError::ArityMismatch {
                        context: format!(
                            "word_translation `{}` step {idx} (`{}`)",
                            tw.after_operation, before_op.name
                        ),
                        expected: before_op.args.len(),
                        actual: step.arg_exprs.len(),
                    });
                }
                for (a_idx, arg_expr) in step.arg_exprs.iter().enumerate() {
                    validate_poly_expr(
                        arg_expr,
                        domain,
                        after_src_coords,
                        &after_args,
                        allowed_params,
                        &format!(
                            "word_translation `{}` step {idx} arg {a_idx}",
                            tw.after_operation
                        ),
                    )?;
                }
                current_phase = before_op.target_phase.as_str();
            }
            if current_phase != expected_end {
                return Err(ValidationError::PhasePathMismatch {
                    after_operation: tw.after_operation.clone(),
                    detail: format!(
                        "translated word ends in phase `{current_phase}`, expected `{expected_end}`"
                    ),
                });
            }
        }
    }
    for op in &after.inner().operations {
        if !seen_ops.contains(&op.name) {
            return Err(ValidationError::MissingWordTranslation {
                after_operation: op.name.clone(),
            });
        }
    }

    Ok(CheckedComparisonPair::from_validated(ComparisonPair {
        before: before.into_inner(),
        after: after.into_inner(),
        state_comparisons: pair.state_comparisons,
        word_translation: pair.word_translation,
    }))
}

pub(crate) fn collect_and_check_param_names(
    spec: &ChangeSpec,
) -> Result<BTreeSet<String>, ValidationError> {
    require_non_empty(&spec.name, "change_spec.name")?;
    validate_coeff_domain(&spec.coeff_domain, &format!("change_spec `{}`", spec.name))?;
    validate_provenance(&spec.provenance, &format!("change_spec `{}`", spec.name))?;
    let mut names = BTreeSet::new();
    for param in &spec.parameters {
        require_non_empty(&param.name, "change_spec.parameter")?;
        validate_opt_source_ref(
            param.provenance.as_ref(),
            &format!("parameter `{}`", param.name),
        )?;
        if !names.insert(param.name.clone()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "parameter",
                name: param.name.clone(),
            });
        }
        validate_coeff_domain(&param.coeff_domain, &format!("parameter `{}`", param.name))?;
        if param.coeff_domain != spec.coeff_domain {
            return Err(ValidationError::DomainMismatch {
                expected: spec.coeff_domain.clone(),
                actual: param.coeff_domain.clone(),
                context: format!("parameter `{}`", param.name),
            });
        }
    }
    Ok(names)
}

fn lookup_presentation<'a>(pair: &'a ComparisonPair, name: &str) -> Option<&'a Presentation> {
    if pair.before.name == name {
        Some(&pair.before)
    } else if pair.after.name == name {
        Some(&pair.after)
    } else {
        None
    }
}

fn collect_presentation_params(pres: &Presentation, out: &mut BTreeSet<String>) {
    for phase in &pres.phases {
        for law in &phase.state_laws {
            law.polynomial.collect_params(out);
        }
    }
    for op in &pres.operations {
        for expr in op.updates.values() {
            expr.collect_params(out);
        }
    }
    for obs in &pres.observations {
        for expr in &obs.components {
            expr.collect_params(out);
        }
    }
}

fn collect_pair_params(pair: &ComparisonPair, out: &mut BTreeSet<String>) {
    collect_presentation_params(&pair.before, out);
    collect_presentation_params(&pair.after, out);
    for sc in &pair.state_comparisons {
        for expr in sc.map.values() {
            expr.collect_params(out);
        }
    }
    for tw in &pair.word_translation.entries {
        for step in &tw.steps {
            for expr in &step.arg_exprs {
                expr.collect_params(out);
            }
        }
    }
}

/// 許容変換仕様 H（`ChangeSpec`）を `CheckedComparisonPair` に対して検証する。
pub fn validate_change_spec(
    spec: ChangeSpec,
    pair: &CheckedComparisonPair,
) -> Result<CheckedChangeSpec, ValidationError> {
    let param_names = collect_and_check_param_names(&spec)?;
    let mut used_params = BTreeSet::new();
    collect_pair_params(pair.inner(), &mut used_params);
    for used in used_params {
        if !param_names.contains(&used) {
            return Err(ValidationError::UnknownRef {
                kind: "parameter",
                name: used,
                context: format!("change_spec `{}` against comparison pair", spec.name),
            });
        }
    }
    validate_change_spec_checked_params(spec, pair)
}

pub(crate) fn validate_change_spec_checked_params(
    spec: ChangeSpec,
    pair: &CheckedComparisonPair,
) -> Result<CheckedChangeSpec, ValidationError> {
    if spec.coeff_domain != pair.inner().before.coeff_domain {
        return Err(ValidationError::DomainMismatch {
            expected: pair.inner().before.coeff_domain.clone(),
            actual: spec.coeff_domain.clone(),
            context: format!("change_spec `{}`", spec.name),
        });
    }

    let mut seen_fixed = BTreeSet::new();
    for fixed in &spec.fixed {
        if !seen_fixed.insert(fixed) {
            return Err(ValidationError::DuplicateDecl {
                kind: "fixed target",
                name: format!("{fixed:?}"),
            });
        }
        validate_fixed_target(fixed, pair.inner())?;
    }
    let mut seen_editable = BTreeSet::new();
    for editable in &spec.editable {
        if !seen_editable.insert(editable) {
            return Err(ValidationError::DuplicateDecl {
                kind: "editable target",
                name: format!("{editable:?}"),
            });
        }
        validate_editable_target(editable, pair.inner())?;
        let counterpart = fixed_counterpart(editable);
        if seen_fixed.contains(&counterpart) {
            return Err(ValidationError::FixedEditableConflict {
                target: format!("{editable:?}"),
            });
        }
    }

    Ok(CheckedChangeSpec::from_validated(spec))
}

fn fixed_counterpart(target: &EditableTarget) -> FixedTarget {
    match target {
        EditableTarget::OperationExpr {
            presentation,
            operation,
        } => FixedTarget::OperationExpr {
            presentation: presentation.clone(),
            operation: operation.clone(),
        },
        EditableTarget::RepresentationLaw {
            presentation,
            phase,
            law,
        } => FixedTarget::RepresentationLaw {
            presentation: presentation.clone(),
            phase: phase.clone(),
            law: law.clone(),
        },
        EditableTarget::StateComparisonExpr { after_phase } => FixedTarget::StateComparisonExpr {
            after_phase: after_phase.clone(),
        },
    }
}

fn validate_fixed_target(
    target: &FixedTarget,
    pair: &ComparisonPair,
) -> Result<(), ValidationError> {
    match target {
        FixedTarget::SemanticLaw {
            presentation,
            phase,
            law,
        }
        | FixedTarget::RepresentationLaw {
            presentation,
            phase,
            law,
        } => {
            let expected_kind = match target {
                FixedTarget::SemanticLaw { .. } => LawKind::Semantic,
                _ => LawKind::Representation,
            };
            let pres = lookup_presentation(pair, presentation).ok_or_else(|| {
                ValidationError::UnknownRef {
                    kind: "presentation",
                    name: presentation.clone(),
                    context: "change_spec.fixed".to_owned(),
                }
            })?;
            let ph = pres
                .phase(phase)
                .ok_or_else(|| ValidationError::UnknownRef {
                    kind: "phase",
                    name: phase.clone(),
                    context: format!("change_spec.fixed ({presentation})"),
                })?;
            let found = ph
                .state_laws
                .iter()
                .find(|l| l.name == *law)
                .ok_or_else(|| ValidationError::UnknownRef {
                    kind: "state_law",
                    name: law.clone(),
                    context: format!("change_spec.fixed ({presentation}.{phase})"),
                })?;
            if found.kind != expected_kind {
                return Err(ValidationError::UnknownRef {
                    kind: expected_kind.wire(),
                    name: format!("{presentation}.{phase}.{law}"),
                    context: "change_spec.fixed law kind mismatch".to_owned(),
                });
            }
            Ok(())
        }
        FixedTarget::OperationExpr {
            presentation,
            operation,
        } => {
            let pres = lookup_presentation(pair, presentation).ok_or_else(|| {
                ValidationError::UnknownRef {
                    kind: "presentation",
                    name: presentation.clone(),
                    context: "change_spec.fixed".to_owned(),
                }
            })?;
            if pres.operation(operation).is_none() {
                return Err(ValidationError::UnknownRef {
                    kind: "operation",
                    name: operation.clone(),
                    context: format!("change_spec.fixed ({presentation})"),
                });
            }
            Ok(())
        }
        FixedTarget::ObservationExpr {
            presentation,
            phase,
            observation,
        } => {
            let pres = lookup_presentation(pair, presentation).ok_or_else(|| {
                ValidationError::UnknownRef {
                    kind: "presentation",
                    name: presentation.clone(),
                    context: "change_spec.fixed".to_owned(),
                }
            })?;
            if !pres
                .observations
                .iter()
                .any(|o| o.phase == *phase && o.name == *observation)
            {
                return Err(ValidationError::UnknownRef {
                    kind: "observation",
                    name: format!("{phase}.{observation}"),
                    context: format!("change_spec.fixed ({presentation})"),
                });
            }
            Ok(())
        }
        FixedTarget::StateComparisonExpr { after_phase } => {
            if !pair
                .state_comparisons
                .iter()
                .any(|sc| sc.after_phase == *after_phase)
            {
                return Err(ValidationError::UnknownRef {
                    kind: "state_comparison",
                    name: after_phase.clone(),
                    context: "change_spec.fixed".to_owned(),
                });
            }
            Ok(())
        }
        FixedTarget::WordTranslationOp { operation } => {
            if pair.word_translation.for_operation(operation).is_none() {
                return Err(ValidationError::UnknownRef {
                    kind: "word_translation",
                    name: operation.clone(),
                    context: "change_spec.fixed".to_owned(),
                });
            }
            Ok(())
        }
    }
}

fn validate_editable_target(
    target: &EditableTarget,
    pair: &ComparisonPair,
) -> Result<(), ValidationError> {
    match target {
        EditableTarget::OperationExpr {
            presentation,
            operation,
        } => {
            let pres = lookup_presentation(pair, presentation).ok_or_else(|| {
                ValidationError::UnknownRef {
                    kind: "presentation",
                    name: presentation.clone(),
                    context: "change_spec.editable".to_owned(),
                }
            })?;
            if pres.operation(operation).is_none() {
                return Err(ValidationError::UnknownRef {
                    kind: "operation",
                    name: operation.clone(),
                    context: format!("change_spec.editable ({presentation})"),
                });
            }
            Ok(())
        }
        EditableTarget::RepresentationLaw {
            presentation,
            phase,
            law,
        } => {
            let pres = lookup_presentation(pair, presentation).ok_or_else(|| {
                ValidationError::UnknownRef {
                    kind: "presentation",
                    name: presentation.clone(),
                    context: "change_spec.editable".to_owned(),
                }
            })?;
            let ph = pres
                .phase(phase)
                .ok_or_else(|| ValidationError::UnknownRef {
                    kind: "phase",
                    name: phase.clone(),
                    context: format!("change_spec.editable ({presentation})"),
                })?;
            let found = ph
                .state_laws
                .iter()
                .find(|l| l.name == *law)
                .ok_or_else(|| ValidationError::UnknownRef {
                    kind: "state_law",
                    name: law.clone(),
                    context: format!("change_spec.editable ({presentation}.{phase})"),
                })?;
            if found.kind == LawKind::Semantic {
                return Err(ValidationError::SemanticLawEditable {
                    presentation: presentation.clone(),
                    phase: phase.clone(),
                    law: law.clone(),
                });
            }
            Ok(())
        }
        EditableTarget::StateComparisonExpr { after_phase } => {
            if !pair
                .state_comparisons
                .iter()
                .any(|sc| sc.after_phase == *after_phase)
            {
                return Err(ValidationError::UnknownRef {
                    kind: "state_comparison",
                    name: after_phase.clone(),
                    context: "change_spec.editable".to_owned(),
                });
            }
            Ok(())
        }
    }
}

/// 評価条件 P（`EvalCondition`）を検証する。
pub fn validate_eval_condition(
    cond: EvalCondition,
    coeff_domain: &CoeffDomain,
    allowed_params: &BTreeSet<String>,
) -> Result<CheckedEvalCondition, ValidationError> {
    validate_allowed_params(allowed_params, "eval_condition.allowed_params")?;
    validate_coeff_domain(coeff_domain, &format!("eval_condition `{}`", cond.name))?;
    validate_eval_condition_checked_params(cond, coeff_domain, allowed_params)
}

pub(crate) fn validate_eval_condition_checked_params(
    cond: EvalCondition,
    coeff_domain: &CoeffDomain,
    allowed_params: &BTreeSet<String>,
) -> Result<CheckedEvalCondition, ValidationError> {
    require_non_empty(&cond.name, "eval_condition.name")?;
    validate_provenance(&cond.provenance, &format!("eval_condition `{}`", cond.name))?;
    validate_point_domain_compatibility(coeff_domain, &cond.point_domain)?;

    validate_named_polys(
        &cond.evaluations,
        "evaluation",
        coeff_domain,
        allowed_params,
    )?;
    validate_named_polys(&cond.equations, "equation", coeff_domain, allowed_params)?;
    validate_named_polys(
        &cond.invertibles,
        "invertible",
        coeff_domain,
        allowed_params,
    )?;

    Ok(CheckedEvalCondition::from_validated(cond))
}

fn validate_point_domain_compatibility(
    coeff_domain: &CoeffDomain,
    point_domain: &PointDomain,
) -> Result<(), ValidationError> {
    if let PointDomain::FiniteFieldPoints(p) = point_domain
        && !is_prime(p)
    {
        return Err(ValidationError::InvalidPrimeModulus {
            modulus: p.clone(),
            context: "eval_condition.point_domain".to_owned(),
        });
    }
    let compatible = match (coeff_domain, point_domain) {
        (_, PointDomain::UniversalRing) => true,
        (CoeffDomain::Q | CoeffDomain::Z, PointDomain::AlgebraicClosure)
        | (CoeffDomain::Q | CoeffDomain::Z, PointDomain::RationalPoints)
        | (CoeffDomain::Z, PointDomain::IntegerPoints) => true,
        (CoeffDomain::Fp(p1), PointDomain::FiniteFieldPoints(p2)) => p1 == p2,
        _ => false,
    };
    if !compatible {
        return Err(ValidationError::PointDomainMismatch {
            coeff_domain: coeff_domain.clone(),
            point_domain: point_domain.clone(),
        });
    }
    Ok(())
}

fn validate_named_polys(
    items: &[NamedPoly],
    kind: &'static str,
    coeff_domain: &CoeffDomain,
    allowed_params: &BTreeSet<String>,
) -> Result<(), ValidationError> {
    let empty_states = BTreeSet::new();
    let empty_args = BTreeSet::new();
    let mut seen = BTreeSet::new();
    for item in items {
        require_non_empty(&item.name, kind)?;
        validate_opt_source_ref(item.provenance.as_ref(), &format!("{kind} `{}`", item.name))?;
        if !seen.insert(item.name.clone()) {
            return Err(ValidationError::DuplicateDecl {
                kind,
                name: item.name.clone(),
            });
        }
        validate_poly_expr(
            &item.expr,
            coeff_domain,
            &empty_states,
            &empty_args,
            allowed_params,
            &format!("{kind} `{}`", item.name),
        )?;
    }
    Ok(())
}
