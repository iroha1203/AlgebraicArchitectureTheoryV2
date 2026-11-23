//! `shigure robustness`・`shigure chevalley`・`shigure observations` 宣言の静的検査。

use super::ast_ext::ShigureScalarLit;
use super::ast_phase3::*;
use super::check::{
    CResult, DeclCategory, check_point_domain, check_presentation_vars, resolve_shigure_ref,
};
use super::check_ext_common::check_scalar_lit;
use super::check_family::{check_family, check_named_polys_in_scope, check_origin_ref};
use super::*;
use crate::law::ast::Span;
use crate::law::check::{Checker, duplicate, full, reference};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;
use std::collections::{BTreeMap, HashMap, HashSet};

pub(super) fn check_all_families<E: InputError>(
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span, usize)>,
    out: &mut CheckedShigureDecls,
    edges: &mut Vec<(usize, usize, Span)>,
    control: &Control,
) -> CResult<(), E> {
    let readings = checker.ast.clone();
    for (r_idx, r) in readings.iter().enumerate() {
        for d in &r.shigure_decls {
            if let ShigureDeclAst::Family(raw) = d {
                E::checkpoint(control, Checkpoint::LawSemantics)?;
                let checked = check_family(
                    raw.as_ref(),
                    r_idx,
                    &r.name.name,
                    checker,
                    index,
                    out,
                    edges,
                    control,
                )?;
                out.families.insert(checked.name.clone(), checked);
            }
        }
    }
    Ok(())
}

pub(super) fn check_all_phase3_tasks<E: InputError>(
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span, usize)>,
    out: &mut CheckedShigureDecls,
    edges: &mut Vec<(usize, usize, Span)>,
    control: &Control,
) -> CResult<(), E> {
    let readings = checker.ast.clone();
    for (r_idx, r) in readings.iter().enumerate() {
        for d in &r.shigure_decls {
            match d {
                ShigureDeclAst::Robustness(raw) => {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    let checked = check_robustness(
                        raw,
                        r_idx,
                        &r.name.name,
                        checker,
                        index,
                        out,
                        edges,
                        control,
                    )?;
                    out.robustness_tasks.insert(checked.name.clone(), checked);
                }
                ShigureDeclAst::Chevalley(raw) => {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    let checked = check_chevalley(
                        raw,
                        r_idx,
                        &r.name.name,
                        checker,
                        index,
                        out,
                        edges,
                        control,
                    )?;
                    out.chevalley_tasks.insert(checked.name.clone(), checked);
                }
                ShigureDeclAst::Observations(raw) => {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    let checked = check_observations(
                        raw,
                        r_idx,
                        &r.name.name,
                        checker,
                        index,
                        out,
                        edges,
                        control,
                    )?;
                    out.observation_tasks.insert(checked.name.clone(), checked);
                }
                _ => {}
            }
        }
    }
    Ok(())
}

fn check_task_point_domain<E: InputError>(
    raw: &RawPointDomain,
    coeff_domain: &ShigureCoeffDomain,
    chevalley_only_closure: bool,
    context: &str,
    control: &Control,
) -> CResult<ShigurePointDomain, E> {
    let pd = check_point_domain(raw, control)?;
    if matches!(pd, ShigurePointDomain::UniversalRing) {
        return Err(Box::new(Issue::law(
            Code::Type,
            span_of_point_domain(raw),
            format!("top-level `point_domain universal_ring` is forbidden in {context}; use `check_universal_ring true;` on compatible tasks"),
        ))
        .into());
    }
    if chevalley_only_closure && !matches!(pd, ShigurePointDomain::AlgebraicClosure) {
        return Err(Box::new(Issue::law(
            Code::Type,
            span_of_point_domain(raw),
            format!(
                "`shigure chevalley` only accepts `point_domain algebraic_closure;` ({context})"
            ),
        ))
        .into());
    }
    let compatible = match (coeff_domain, &pd) {
        (ShigureCoeffDomain::Q | ShigureCoeffDomain::Z, ShigurePointDomain::AlgebraicClosure)
        | (ShigureCoeffDomain::Q | ShigureCoeffDomain::Z, ShigurePointDomain::RationalPoints)
        | (ShigureCoeffDomain::Z, ShigurePointDomain::IntegerPoints) => true,
        (ShigureCoeffDomain::Fp(p1), ShigurePointDomain::FiniteFieldPoints(p2)) => p1 == p2,
        _ => false,
    };
    if !compatible {
        return Err(Box::new(Issue::law(
            Code::Type,
            span_of_point_domain(raw),
            format!("point_domain is incompatible with family coefficient domain in {context}"),
        ))
        .into());
    }
    Ok(pd)
}

fn span_of_point_domain(raw: &RawPointDomain) -> Span {
    match raw {
        RawPointDomain::AlgebraicClosure(s)
        | RawPointDomain::RationalPoints(s)
        | RawPointDomain::IntegerPoints(s)
        | RawPointDomain::UniversalRing(s)
        | RawPointDomain::FiniteFieldPoints { span: s, .. } => *s,
    }
}

fn check_base_vec<E: InputError>(
    lits: &[ShigureScalarLit],
    expected_len: usize,
    coeff_domain: &ShigureCoeffDomain,
    span: Span,
    label: &str,
    control: &Control,
) -> CResult<(), E> {
    if lits.len() != expected_len {
        return Err(Box::new(Issue::law(
            Code::Type,
            span,
            format!(
                "{label} length ({}) must match base dimension ({expected_len})",
                lits.len()
            ),
        ))
        .into());
    }
    for lit in lits {
        check_scalar_lit(lit, coeff_domain, span, control)?;
    }
    Ok(())
}

fn check_candidate_selector<E: InputError>(
    sel: &RawCandidateSelector,
    fam: &ShigureFamilySpec,
    span: Span,
    context: &str,
    control: &Control,
) -> CResult<ShigureCandidateSelector, E> {
    match sel {
        RawCandidateSelector::ById(id) => match &fam.candidates.space {
            ShigureCandidateSpace::FiniteMembers(members) => {
                if !members.iter().any(|m| m.id == id.name) {
                    return reference(
                        id.span,
                        format!("unknown designated candidate id `{}` in {context}", id.name),
                    );
                }
                Ok(ShigureCandidateSelector::ById(id.name.clone()))
            }
            ShigureCandidateSpace::PolynomialScheme { .. } => Err(Box::new(Issue::law(
                Code::Type,
                id.span,
                format!(
                    "`designated_candidate id` cannot target a candidate `scheme` in {context}"
                ),
            ))
            .into()),
        },
        RawCandidateSelector::ByValues(pairs) => {
            let c_set: HashSet<&str> = fam.candidates.c_vars.iter().map(String::as_str).collect();
            let mut out = BTreeMap::new();
            for (var, lit, v_span) in pairs {
                if !c_set.contains(var.name.as_str()) {
                    return reference(
                        var.span,
                        format!("unknown candidate variable `{}` in {context}", var.name),
                    );
                }
                if out.contains_key(&var.name) {
                    return duplicate(
                        var.span,
                        format!(
                            "duplicate designated candidate assignment `{}` in {context}",
                            var.name
                        ),
                    );
                }
                check_scalar_lit(lit, &fam.coeff_domain, *v_span, control)?;
                out.insert(var.name.clone(), lit.clone());
            }
            for req in &fam.candidates.c_vars {
                if !out.contains_key(req) {
                    return Err(Box::new(Issue::law(
                        Code::Type,
                        span,
                        format!("missing candidate variable `{req}` in `designated_candidate values` ({context})"),
                    ))
                    .into());
                }
            }
            Ok(ShigureCandidateSelector::ByValues(out))
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn check_robustness<E: InputError>(
    raw: &RawRobustnessTask,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span, usize)>,
    decls: &CheckedShigureDecls,
    edges: &mut Vec<(usize, usize, Span)>,
    control: &Control,
) -> CResult<ShigureRobustnessTask, E> {
    let full_name = full(reading_name, &[&raw.name.name]);
    let family_name = resolve_shigure_ref(
        &raw.family,
        DeclCategory::Family,
        r_idx,
        reading_name,
        checker,
        index,
        edges,
    )?;
    let fam = &decls.families[&family_name];
    let point_domain = check_task_point_domain(
        &raw.point_domain,
        &fam.coeff_domain,
        false,
        &full_name,
        control,
    )?;
    check_base_vec(
        &raw.base_value,
        fam.realizations.b_vars.len(),
        &fam.coeff_domain,
        raw.span,
        &format!("{full_name}.base_value"),
        control,
    )?;
    if let Some(fbv) = &raw.fine_base_value {
        let Some(rc) = &fam.reading_comparison else {
            return Err(Box::new(Issue::law(
                Code::Type,
                raw.span,
                format!("`fine_base_value` in `{full_name}` requires `reading_comparison` on family `{family_name}`"),
            ))
            .into());
        };
        check_base_vec(
            fbv,
            rc.fine_b_vars.len(),
            &fam.coeff_domain,
            raw.span,
            &format!("{full_name}.fine_base_value"),
            control,
        )?;
    }
    let designated = raw
        .designated_candidate
        .as_ref()
        .map(|s| check_candidate_selector(s, fam, raw.span, &full_name, control))
        .transpose()?;
    Ok(ShigureRobustnessTask {
        name: full_name,
        reading: reading_name.to_owned(),
        family: family_name,
        point_domain,
        base_value: raw.base_value.clone(),
        designated_candidate: designated,
        check_universal_ring: raw.check_universal_ring,
        fine_base_value: raw.fine_base_value.clone(),
        span: raw.span,
    })
}

#[allow(clippy::too_many_arguments)]
fn check_chevalley<E: InputError>(
    raw: &RawChevalleyTask,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span, usize)>,
    decls: &CheckedShigureDecls,
    edges: &mut Vec<(usize, usize, Span)>,
    control: &Control,
) -> CResult<ShigureChevalleyTask, E> {
    let full_name = full(reading_name, &[&raw.name.name]);
    let family_name = resolve_shigure_ref(
        &raw.family,
        DeclCategory::Family,
        r_idx,
        reading_name,
        checker,
        index,
        edges,
    )?;
    let fam = &decls.families[&family_name];
    let point_domain = check_task_point_domain(
        &raw.point_domain,
        &fam.coeff_domain,
        true,
        &full_name,
        control,
    )?;
    if let Some(bv) = &raw.base_value {
        check_base_vec(
            bv,
            fam.realizations.b_vars.len(),
            &fam.coeff_domain,
            raw.span,
            &format!("{full_name}.base_value"),
            control,
        )?;
    }
    let designated = raw
        .designated_candidate
        .as_ref()
        .map(|s| check_candidate_selector(s, fam, raw.span, &full_name, control))
        .transpose()?;

    let u_set: HashSet<&str> = fam.realizations.u_vars.iter().map(String::as_str).collect();
    let c_set: HashSet<&str> = fam.candidates.c_vars.iter().map(String::as_str).collect();
    let mut probe_names = HashSet::new();
    let mut probes = Vec::with_capacity(raw.probes.len());
    for p in &raw.probes {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !probe_names.insert(p.name.name.clone()) {
            return duplicate(
                p.name.span,
                format!("duplicate probe `{}` in `{full_name}`", p.name.name),
            );
        }
        let mut u_assignments = BTreeMap::new();
        let mut c_assignments = BTreeMap::new();
        for (var, lit, span) in &p.assignments {
            check_scalar_lit(lit, &fam.coeff_domain, *span, control)?;
            if u_set.contains(var.name.as_str()) {
                if u_assignments
                    .insert(var.name.clone(), lit.clone())
                    .is_some()
                {
                    return duplicate(
                        var.span,
                        format!(
                            "duplicate assignment `{}` in probe `{}`",
                            var.name, p.name.name
                        ),
                    );
                }
            } else if c_set.contains(var.name.as_str()) {
                if c_assignments
                    .insert(var.name.clone(), lit.clone())
                    .is_some()
                {
                    return duplicate(
                        var.span,
                        format!(
                            "duplicate assignment `{}` in probe `{}`",
                            var.name, p.name.name
                        ),
                    );
                }
            } else {
                return reference(
                    var.span,
                    format!(
                        "unknown realization or candidate variable `{}` in probe `{}` ({full_name})",
                        var.name, p.name.name
                    ),
                );
            }
        }
        probes.push(ShigureRationalProbe {
            name: p.name.name.clone(),
            u_assignments,
            c_assignments,
            span: p.span,
        });
    }
    Ok(ShigureChevalleyTask {
        name: full_name,
        reading: reading_name.to_owned(),
        family: family_name,
        point_domain,
        base_value: raw.base_value.clone(),
        designated_candidate: designated,
        probes,
        check_global_regular_section: raw.check_global_regular_section,
        check_universal_ring: raw.check_universal_ring,
        span: raw.span,
    })
}

#[allow(clippy::too_many_arguments)]
fn check_observations<E: InputError>(
    raw: &RawObservationTask,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span, usize)>,
    decls: &CheckedShigureDecls,
    edges: &mut Vec<(usize, usize, Span)>,
    control: &Control,
) -> CResult<ShigureObservationTask, E> {
    let full_name = full(reading_name, &[&raw.name.name]);
    let family_name = resolve_shigure_ref(
        &raw.family,
        DeclCategory::Family,
        r_idx,
        reading_name,
        checker,
        index,
        edges,
    )?;
    let fam = &decls.families[&family_name];
    let point_domain = check_task_point_domain(
        &raw.point_domain,
        &fam.coeff_domain,
        false,
        &full_name,
        control,
    )?;
    check_base_vec(
        &raw.base_value,
        fam.realizations.b_vars.len(),
        &fam.coeff_domain,
        raw.span,
        &format!("{full_name}.base_value"),
        control,
    )?;

    let u_set: HashSet<&str> = fam.realizations.u_vars.iter().map(String::as_str).collect();
    let mut obs_ids = HashSet::new();
    let mut with_cost = 0usize;
    let mut without_cost = 0usize;
    let mut observations = Vec::with_capacity(raw.observations.len());

    for obs in &raw.observations {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !obs_ids.insert(obs.id.name.clone()) {
            return duplicate(
                obs.id.span,
                format!("duplicate observation `{}` in `{full_name}`", obs.id.name),
            );
        }
        if obs.components.is_empty() {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                obs.span,
                format!(
                    "`observe {}` requires at least one `component` in `{full_name}`",
                    obs.id.name
                ),
            ))
            .into());
        }
        let origin =
            check_origin_ref(&obs.origin, &format!("{full_name}.observe.{}", obs.id.name))?;
        let components = check_named_polys_in_scope(
            &obs.components,
            &fam.coeff_domain,
            &u_set,
            &format!("{full_name}.observe.{}", obs.id.name),
            control,
        )?;
        let cost = match &obs.cost {
            Some((c, _)) => {
                with_cost += 1;
                Some(c.clone())
            }
            None => {
                without_cost += 1;
                None
            }
        };
        observations.push(ShigureCandidateObservationDecl {
            id: obs.id.name.clone(),
            components,
            cost,
            origin,
            span: obs.span,
        });
    }

    if with_cost > 0 && without_cost > 0 {
        return Err(Box::new(Issue::law(
            Code::Type,
            raw.span,
            format!("`{full_name}` must specify `cost` on either every `observe` block or none"),
        ))
        .into());
    }

    let law_readout = raw
        .law_readout
        .as_ref()
        .map(|lr| {
            if lr.components.is_empty() {
                return Err(Box::new(Issue::law(
                    Code::Syntax,
                    lr.span,
                    format!(
                        "`law_readout {}` requires at least one `component` in `{full_name}`",
                        lr.name.name
                    ),
                ))
                .into());
            }
            let components = check_named_polys_in_scope::<E>(
                &lr.components,
                &fam.coeff_domain,
                &u_set,
                &format!("{full_name}.law_readout.{}", lr.name.name),
                control,
            )?;
            Ok::<_, E>(ShigureLawReadoutDecl {
                name: lr.name.name.clone(),
                components,
                span: lr.span,
            })
        })
        .transpose()?;

    Ok(ShigureObservationTask {
        name: full_name,
        reading: reading_name.to_owned(),
        family: family_name,
        point_domain,
        base_value: raw.base_value.clone(),
        observations,
        law_readout,
        span: raw.span,
    })
}

pub(super) fn check_raw_sequence<E: InputError>(
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
        let Some(p_name) = &m.presentation else {
            return Err(Box::new(Issue::law(
                Code::Type,
                m.span,
                format!(
                    "`raw_sequence` in `{full_name}` requires realization member `{}` to specify `presentation`",
                    m.id
                ),
            ))
            .into());
        };
        let pres = &decls.presentations[p_name];
        check_presentation_vars(pres, None, control)?;
        let Some(start_ph) = pres.phases.iter().find(|p| p.name == raw.start_phase.name) else {
            return reference(
                raw.start_phase.span,
                format!(
                    "unknown phase `{}` in presentation `{p_name}`",
                    raw.start_phase.name
                ),
            );
        };
        let ph_coords: HashSet<&str> = start_ph.coords.iter().map(|c| c.name.as_str()).collect();
        for k in start_state.keys() {
            if !ph_coords.contains(k.as_str()) {
                return reference(
                    raw.span,
                    format!(
                        "unknown start_state coordinate `{k}` for `{p_name}.{}` in `{full_name}`",
                        start_ph.name
                    ),
                );
            }
        }
        for c in &start_ph.coords {
            if matches!(c.binding, ShigureCoordBinding::Symbolic)
                && !start_state.contains_key(&c.name)
            {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    raw.span,
                    format!(
                        "start_state in `{full_name}` is missing symbolic coordinate `{}` of `{p_name}.{}`",
                        c.name, start_ph.name
                    ),
                ))
                .into());
            }
        }
        let mut cur_phase = raw.start_phase.name.as_str();
        let mut baseline_phase: Option<&str> = match raw.baseline_step_index {
            None if steps.len() == 1 => Some(raw.start_phase.name.as_str()),
            _ => None,
        };
        let effective_baseline_idx = raw
            .baseline_step_index
            .unwrap_or_else(|| steps.len().saturating_sub(2));
        for (idx, (op_name, args)) in steps.iter().enumerate() {
            let Some(op) = pres.operations.iter().find(|o| &o.name == op_name) else {
                return reference(
                    raw.span,
                    format!("unknown step operation `{op_name}` in `{p_name}`"),
                );
            };
            if op.source_phase != cur_phase {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    raw.span,
                    format!(
                        "`raw_sequence` step {idx} (`{op_name}`) in `{full_name}` expects source phase `{}`, got `{cur_phase}`",
                        op.source_phase
                    ),
                ))
                .into());
            }
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
            cur_phase = op.target_phase.as_str();
            if baseline_phase.is_none() && idx == effective_baseline_idx {
                baseline_phase = Some(cur_phase);
            }
        }
        let Some(final_obs) = pres
            .observations
            .iter()
            .find(|o| o.name == raw.observation_name.name && o.phase == cur_phase)
        else {
            return reference(
                raw.observation_name.span,
                format!(
                    "unknown observation `{}` on terminal phase `{cur_phase}` in `{p_name}`",
                    raw.observation_name.name
                ),
            );
        };
        if let Some(b_phase) = baseline_phase {
            let Some(base_obs) = pres
                .observations
                .iter()
                .find(|o| o.name == raw.observation_name.name && o.phase == b_phase)
            else {
                return reference(
                    raw.observation_name.span,
                    format!(
                        "unknown observation `{}` on baseline phase `{b_phase}` in `{p_name}`",
                        raw.observation_name.name
                    ),
                );
            };
            if final_obs.components.len() != base_obs.components.len() {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    raw.span,
                    format!(
                        "observation `{}` arity mismatch between baseline `{b_phase}` ({}) and terminal `{cur_phase}` ({}) in `{p_name}`",
                        raw.observation_name.name,
                        base_obs.components.len(),
                        final_obs.components.len()
                    ),
                ))
                .into());
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
