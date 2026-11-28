//! `shigure revision`・`shigure multisource` 宣言の静的意味検査（AC2）。

use super::ast_phase3::{RawMemberCoordValue, ShigureMemberCoordValue};
use super::ast_phase5_rev::*;
use super::check::{CResult, CoordCheckCtx, check_coeff_domain, check_member_coord_value};
use super::check_ext_common::check_scalar_lit;
use super::check_family::check_origin_ref;
use super::check_phase4_lift_artin::{check_p4_origins, p4_type_err};
use super::check_phase5_common::{
    check_nonnegative_cost_lit, check_p5_coord_assignments, check_p5_revision_constraints,
    check_p5_revision_coords,
};
use super::*;
use crate::law::check::{Checker, duplicate, full, reference};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::json::InputError;
use std::collections::HashSet;

pub(super) fn check_all_phase5_tasks<E: InputError>(
    checker: &Checker<'_, E>,
    out: &mut CheckedShigureDecls,
    control: &Control,
) -> CResult<(), E> {
    let readings = checker.ast.clone();
    for (r_idx, r) in readings.iter().enumerate() {
        for d in &r.shigure_decls {
            match d {
                ShigureDeclAst::Occurrence(raw) => {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    let checked = super::check_phase5_occ::check_occurrence(
                        raw.as_ref(),
                        r_idx,
                        &r.name.name,
                        checker,
                        control,
                    )?;
                    out.occurrence_tasks.insert(checked.name.clone(), checked);
                }
                ShigureDeclAst::Partial(raw) => {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    let checked = super::check_phase5_partial::check_partial(
                        raw.as_ref(),
                        r_idx,
                        &r.name.name,
                        checker,
                        control,
                    )?;
                    out.partial_tasks.insert(checked.name.clone(), checked);
                }
                ShigureDeclAst::Revision(raw) => {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    let checked =
                        check_revision(raw.as_ref(), r_idx, &r.name.name, checker, control)?;
                    out.revision_tasks.insert(checked.name.clone(), checked);
                }
                ShigureDeclAst::Multisource(raw) => {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    let checked =
                        check_multisource(raw.as_ref(), r_idx, &r.name.name, checker, control)?;
                    out.multisource_tasks.insert(checked.name.clone(), checked);
                }
                _ => {}
            }
        }
    }
    Ok(())
}

fn check_matrix<E: InputError>(
    rows: &[Vec<RawMemberCoordValue>],
    num_cols: usize,
    coord_ctx: &CoordCheckCtx<'_, '_, E>,
    span: crate::law::ast::Span,
    label: &str,
) -> CResult<Vec<Vec<ShigureMemberCoordValue>>, E> {
    let mut out = Vec::with_capacity(rows.len());
    for row in rows {
        if row.len() != num_cols {
            return p4_type_err(
                span,
                format!("{label} row width {} != num_cols {num_cols}", row.len()),
            );
        }
        out.push(
            row.iter()
                .map(|v| check_member_coord_value(v, coord_ctx, span))
                .collect::<CResult<Vec<_>, E>>()?,
        );
    }
    Ok(out)
}

fn check_snf_revision<E: InputError>(
    raw: &RawSnfRevision,
    r_idx: usize,
    checker: &Checker<'_, E>,
    control: &Control,
) -> CResult<ShigureSnfRevision, E> {
    let coeff_domain = check_coeff_domain(&raw.domain, control)?;
    if !matches!(coeff_domain, ShigureCoeffDomain::Z | ShigureCoeffDomain::Q) {
        return p4_type_err(raw.span, "SNF revision requires Z or Q coefficient domain");
    }
    let ctx = CoordCheckCtx {
        coeff_domain: &coeff_domain,
        r_idx,
        checker,
        control,
    };
    let operator = match &raw.operator {
        RawSnfOperatorMode::Common(rows) => {
            if rows.len() != raw.rhs_before.len() || rows.len() != raw.rhs_after.len() {
                return p4_type_err(
                    raw.span,
                    format!(
                        "snf common_operator rows ({}) must match rhs_before ({}) and rhs_after ({})",
                        rows.len(),
                        raw.rhs_before.len(),
                        raw.rhs_after.len()
                    ),
                );
            }
            ShigureSnfOperatorMode::Common(check_matrix(
                rows,
                raw.num_cols,
                &ctx,
                raw.span,
                "snf.common_operator",
            )?)
        }
        RawSnfOperatorMode::Split { before, after } => {
            if before.len() != raw.rhs_before.len() {
                return p4_type_err(
                    raw.span,
                    format!(
                        "snf operator_before rows ({}) != rhs_before ({})",
                        before.len(),
                        raw.rhs_before.len()
                    ),
                );
            }
            if after.len() != raw.rhs_after.len() {
                return p4_type_err(
                    raw.span,
                    format!(
                        "snf operator_after rows ({}) != rhs_after ({})",
                        after.len(),
                        raw.rhs_after.len()
                    ),
                );
            }
            ShigureSnfOperatorMode::Split {
                before: check_matrix(before, raw.num_cols, &ctx, raw.span, "snf.operator_before")?,
                after: check_matrix(after, raw.num_cols, &ctx, raw.span, "snf.operator_after")?,
            }
        }
    };
    let rhs_before = raw
        .rhs_before
        .iter()
        .map(|v| check_member_coord_value(v, &ctx, raw.span))
        .collect::<CResult<Vec<_>, E>>()?;
    let rhs_after = raw
        .rhs_after
        .iter()
        .map(|v| check_member_coord_value(v, &ctx, raw.span))
        .collect::<CResult<Vec<_>, E>>()?;
    Ok(ShigureSnfRevision {
        coeff_domain,
        num_cols: raw.num_cols,
        operator,
        rhs_before,
        rhs_after,
        operator_unobserved: raw
            .operator_unobserved
            .iter()
            .map(|i| i.name.clone())
            .collect(),
        force_reuse_existing_snf: raw.force_reuse_existing_snf,
        origin_label_only: raw.origin_label_only,
        span: raw.span,
    })
}

fn check_revision<E: InputError>(
    raw: &RawRevisionTask,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    control: &Control,
) -> CResult<ShigureRevisionTask, E> {
    let context = format!("`shigure revision` `{}`", raw.name.name);
    let origins = check_p4_origins(&raw.origins, raw.span, &context)?;
    let coeff_domain = check_coeff_domain(&raw.domain, control)?;
    let (coords, coord_names) =
        check_p5_revision_coords(&raw.coords, &coeff_domain, control, &context)?;
    let shared_constraints = check_p5_revision_constraints(
        &raw.shared_constraints,
        &coord_names,
        &coeff_domain,
        control,
        &context,
    )?;

    let coord_ctx = CoordCheckCtx {
        coeff_domain: &coeff_domain,
        r_idx,
        checker,
        control,
    };
    let check_side = |side: &RawRevisionSide, label: &str| -> CResult<ShigureRevisionSide, E> {
        Ok(ShigureRevisionSide {
            assignments: check_p5_coord_assignments(
                &side.assignments,
                &coord_names,
                &coord_ctx,
                &format!("{context} {label}"),
            )?,
            extra_constraints: check_p5_revision_constraints(
                &side.extra_constraints,
                &coord_names,
                &coeff_domain,
                control,
                &format!("{context} {label}"),
            )?,
            span: side.span,
        })
    };
    let before = check_side(&raw.before, "before")?;
    let after = check_side(&raw.after, "after")?;

    let mut explicit_delta_coords = Vec::with_capacity(raw.explicit_delta_coords.len());
    for d in &raw.explicit_delta_coords {
        if !coord_names.contains(&d.name) {
            return reference(
                d.span,
                format!("unknown coord `{}` in explicit_delta ({context})", d.name),
            );
        }
        explicit_delta_coords.push(d.name.clone());
    }

    let mut probes = Vec::with_capacity(raw.probes.len());
    for p in &raw.probes {
        if !coord_names.contains(&p.target_coord.name) {
            return reference(
                p.target_coord.span,
                format!(
                    "unknown target coord `{}` in probe `{}`",
                    p.target_coord.name, p.name.name
                ),
            );
        }
        let mut sup = HashSet::new();
        let mut support = Vec::with_capacity(p.support.len());
        for s in &p.support {
            if !coord_names.contains(&s.name) {
                return reference(
                    s.span,
                    format!(
                        "unknown coord `{}` in probe `{}` support",
                        s.name, p.name.name
                    ),
                );
            }
            sup.insert(s.name.as_str());
            support.push(s.name.clone());
        }
        if !sup.contains(p.target_coord.name.as_str()) {
            return p4_type_err(
                p.span,
                format!(
                    "probe `{}` support must include `{}`",
                    p.name.name, p.target_coord.name
                ),
            );
        }
        check_scalar_lit(&p.expected_value, &coeff_domain, p.span, control)?;
        if let (Some(ac), Some(av)) = (&p.antecedent_coord, &p.antecedent_value) {
            if !coord_names.contains(&ac.name) {
                return reference(
                    ac.span,
                    format!(
                        "unknown antecedent coord `{}` in probe `{}`",
                        ac.name, p.name.name
                    ),
                );
            }
            if !sup.contains(ac.name.as_str()) {
                return p4_type_err(
                    p.span,
                    format!(
                        "probe `{}` support must include antecedent `{}`",
                        p.name.name, ac.name
                    ),
                );
            }
            check_scalar_lit(av, &coeff_domain, p.span, control)?;
        }
        probes.push(ShigureRevisionEvalProbe {
            name: p.name.name.clone(),
            support,
            target_coord: p.target_coord.name.clone(),
            expected_value: p.expected_value.clone(),
            antecedent_coord: p.antecedent_coord.as_ref().map(|c| c.name.clone()),
            antecedent_value: p.antecedent_value.clone(),
            span: p.span,
        });
    }

    let snf = match &raw.snf {
        Some(s) => Some(check_snf_revision(s, r_idx, checker, control)?),
        None => None,
    };

    Ok(ShigureRevisionTask {
        name: full(reading_name, &[&raw.name.name]),
        reading: reading_name.to_owned(),
        kind: raw.kind,
        coeff_domain,
        origins,
        coords,
        shared_constraints,
        before,
        after,
        explicit_delta_coords,
        probes,
        snf,
        max_completions: raw.max_completions.unwrap_or(0),
        span: raw.span,
    })
}

fn check_multisource<E: InputError>(
    raw: &RawMultisourceTask,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    control: &Control,
) -> CResult<ShigureMultisourceTask, E> {
    let context = format!("`shigure multisource` `{}`", raw.name.name);
    let origins = check_p4_origins(&raw.origins, raw.span, &context)?;
    let coeff_domain = check_coeff_domain(&raw.domain, control)?;
    let (coords, coord_names) =
        check_p5_revision_coords(&raw.coords, &coeff_domain, control, &context)?;
    let background_constraints = check_p5_revision_constraints(
        &raw.background_constraints,
        &coord_names,
        &coeff_domain,
        control,
        &context,
    )?;

    let coord_ctx = CoordCheckCtx {
        coeff_domain: &coeff_domain,
        r_idx,
        checker,
        control,
    };
    let mut source_ids = HashSet::new();
    let mut sources = Vec::with_capacity(raw.sources.len());
    for src in &raw.sources {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !source_ids.insert(src.source_id.name.as_str()) {
            return duplicate(
                src.source_id.span,
                format!("duplicate source `{}` in {context}", src.source_id.name),
            );
        }
        let origin = check_origin_ref(
            &src.origin,
            &format!("{context} source `{}`", src.source_id.name),
        )?;
        let assignments = check_p5_coord_assignments(
            &src.assignments,
            &coord_names,
            &coord_ctx,
            &format!("source `{}`", src.source_id.name),
        )?;
        let mut forbidden_values = Vec::with_capacity(src.forbidden_values.len());
        for (c, v, v_span) in &src.forbidden_values {
            if !coord_names.contains(&c.name) {
                return reference(
                    c.span,
                    format!(
                        "unknown coord `{}` in source `{}` forbidden",
                        c.name, src.source_id.name
                    ),
                );
            }
            forbidden_values.push((
                c.name.clone(),
                check_member_coord_value(v, &coord_ctx, *v_span)?,
            ));
        }
        let extra_constraints = check_p5_revision_constraints(
            &src.extra_constraints,
            &coord_names,
            &coeff_domain,
            control,
            &format!("source `{}`", src.source_id.name),
        )?;
        sources.push(ShigureSourcePresentation {
            source_id: src.source_id.name.clone(),
            origin,
            assignments,
            forbidden_values,
            extra_constraints,
            span: src.span,
        });
    }

    let support_goal = match &raw.support_goal {
        Some(sg) => {
            let trusted_assignments = check_p5_coord_assignments(
                &sg.trusted_assignments,
                &coord_names,
                &coord_ctx,
                "support_goal.trusted",
            )?;
            let mut cand_ids = HashSet::new();
            let mut with_cost = 0usize;
            let mut without_cost = 0usize;
            let mut candidates = Vec::with_capacity(sg.candidates.len());
            for cand in &sg.candidates {
                if !cand_ids.insert(cand.id.name.as_str()) {
                    return duplicate(
                        cand.id.span,
                        format!("duplicate candidate `{}`", cand.id.name),
                    );
                }
                let origin =
                    check_origin_ref(&cand.origin, &format!("candidate `{}`", cand.id.name))?;
                if !coord_names.contains(&cand.coord.name) {
                    return reference(
                        cand.coord.span,
                        format!(
                            "unknown coord `{}` in candidate `{}`",
                            cand.coord.name, cand.id.name
                        ),
                    );
                }
                let value = check_member_coord_value(&cand.value, &coord_ctx, cand.span)?;
                let cost = match &cand.cost {
                    Some((c, c_span)) => {
                        with_cost += 1;
                        check_nonnegative_cost_lit(
                            c,
                            *c_span,
                            &format!("candidate `{}`", cand.id.name),
                        )?;
                        Some(c.clone())
                    }
                    None => {
                        without_cost += 1;
                        None
                    }
                };
                let verified_actual_value = match &cand.verified_actual_value {
                    Some((v, v_span)) => Some(check_member_coord_value(v, &coord_ctx, *v_span)?),
                    None => None,
                };
                candidates.push(ShigureCandidateRecord {
                    id: cand.id.name.clone(),
                    coord: cand.coord.name.clone(),
                    value,
                    cost,
                    origin,
                    verified_actual_value,
                    span: cand.span,
                });
            }
            if with_cost > 0 && without_cost > 0 {
                return p4_type_err(
                    sg.span,
                    "candidates must either all specify `cost` or none specify `cost`",
                );
            }
            let goal = match &sg.goal {
                RawSupportGoalFormula::CoordEquality(a, b, _) => {
                    for x in [a, b] {
                        if !coord_names.contains(&x.name) {
                            return reference(
                                x.span,
                                format!("unknown coord `{}` in support_goal", x.name),
                            );
                        }
                    }
                    ShigureSupportGoalFormula::CoordEquality(a.name.clone(), b.name.clone())
                }
                RawSupportGoalFormula::CoordEqualsConst(c, v, g_span) => {
                    if !coord_names.contains(&c.name) {
                        return reference(
                            c.span,
                            format!("unknown coord `{}` in support_goal", c.name),
                        );
                    }
                    check_scalar_lit(v, &coeff_domain, *g_span, control)?;
                    ShigureSupportGoalFormula::CoordEqualsConst(c.name.clone(), v.clone())
                }
            };
            Some(ShigureSupportGoalSpec {
                trusted_assignments,
                candidates,
                goal,
                expected_truth: sg.expected_truth,
                check_post_adoption_stability: sg.check_post_adoption_stability,
                span: sg.span,
            })
        }
        None => None,
    };

    Ok(ShigureMultisourceTask {
        name: full(reading_name, &[&raw.name.name]),
        reading: reading_name.to_owned(),
        coeff_domain,
        origins,
        coords,
        background_constraints,
        sources,
        support_goal,
        max_sources_subset_steps: raw.max_sources_subset_steps.unwrap_or(0),
        max_results: raw.max_results.unwrap_or(0),
        span: raw.span,
    })
}
