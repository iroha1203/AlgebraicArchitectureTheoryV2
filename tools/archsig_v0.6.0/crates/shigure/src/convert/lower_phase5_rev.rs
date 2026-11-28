//! `CheckedInputs` から `CheckedRevisionTask` / `CheckedMultisourceTask` への lowering（Phase 5 / 第19章）。

use super::lower::lower_coeff_domain;
use super::lower_expr::{conv_err, lower_scalar_lit, resolve_observed_coord};
use super::lower_family::lower_shigure_origin;
use super::lower_morphism::{ensure_snapshot_exists, select_named_decl};
use super::lower_phase4_lift_artin::lower_p4_origins;
use super::lower_phase5_partial::lower_required_scalar;
use crate::ir::multisource::{
    CandidateRecordSpec, CheckedMultisourceTask, MultisourceTaskSpec, SourcePresentationSpec,
    SupportGoalFormula, SupportGoalSpec,
};
use crate::ir::presentation::CoordValue;
use crate::ir::provenance::{Provenance, SourceRef};
use crate::ir::revision::{
    CheckedRevisionTask, RevisionConstraintSpec, RevisionCoordSpec, RevisionEvalProbe,
    RevisionKind, RevisionPredicate, RevisionSideSpec, RevisionTaskSpec, SnfRevisionSpec,
};
use crate::ir::term::{CoeffDomain, ScalarLit};
use crate::ir::validate::ValidationError;
use archsig_input::archmap::CheckedArchMap;
use archsig_input::input::CheckedInputs;
use archsig_input::law::shigure::{
    ShigureMemberCoordValue, ShigureOriginRef, ShigureRevisionConstraint, ShigureRevisionCoord,
    ShigureRevisionKind, ShigureRevisionPredicate, ShigureSnfOperatorMode,
    ShigureSupportGoalFormula,
};
use std::collections::{BTreeMap, BTreeSet};

fn lower_coords(
    raw: &[ShigureRevisionCoord],
    coeff_domain: &CoeffDomain,
    context: &str,
) -> Result<Vec<RevisionCoordSpec>, ValidationError> {
    raw.iter()
        .map(|c| {
            let domain_values = c
                .domain_values
                .iter()
                .map(|v| lower_scalar_lit(v, coeff_domain, context))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(RevisionCoordSpec {
                id: c.id.clone(),
                domain_values,
            })
        })
        .collect()
}

fn lower_constraints(
    raw: &[ShigureRevisionConstraint],
    coeff_domain: &CoeffDomain,
    context: &str,
) -> Result<Vec<RevisionConstraintSpec>, ValidationError> {
    raw.iter()
        .map(|con| {
            let predicate = match &con.predicate {
                ShigureRevisionPredicate::Equality(a, b) => {
                    RevisionPredicate::Equality(a.clone(), b.clone())
                }
                ShigureRevisionPredicate::LinearZero { terms } => RevisionPredicate::LinearZero {
                    terms: terms
                        .iter()
                        .map(|(k, c)| Ok((lower_scalar_lit(k, coeff_domain, context)?, c.clone())))
                        .collect::<Result<Vec<_>, ValidationError>>()?,
                },
                ShigureRevisionPredicate::AllowedTuples { coords, tuples } => {
                    RevisionPredicate::AllowedTuples {
                        coords: coords.clone(),
                        tuples: tuples
                            .iter()
                            .map(|row| {
                                row.iter()
                                    .map(|v| lower_scalar_lit(v, coeff_domain, context))
                                    .collect::<Result<Vec<_>, _>>()
                            })
                            .collect::<Result<Vec<_>, _>>()?,
                    }
                }
            };
            Ok(RevisionConstraintSpec {
                id: con.id.clone(),
                support: con.support.clone(),
                predicate,
            })
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn lower_optional_assignments(
    raw: &[(String, ShigureMemberCoordValue)],
    archmap: &CheckedArchMap,
    snapshot_id: Option<&str>,
    coeff_domain: &CoeffDomain,
    fallback_ref: &SourceRef,
    scope: &str,
    origins: &mut BTreeSet<SourceRef>,
    missing_slots: &mut Vec<String>,
) -> Result<BTreeMap<String, ScalarLit>, ValidationError> {
    let mut out = BTreeMap::new();
    for (coord, val) in raw {
        match val {
            ShigureMemberCoordValue::Literal(lit) => {
                out.insert(
                    coord.clone(),
                    lower_scalar_lit(lit, coeff_domain, &format!("{scope}.{coord}"))?,
                );
            }
            ShigureMemberCoordValue::ObservedField { entity, field, .. } => {
                let (cv, refs) = resolve_observed_coord(
                    archmap,
                    snapshot_id,
                    entity,
                    field,
                    coeff_domain,
                    fallback_ref,
                )?;
                for r in refs {
                    origins.insert(r);
                }
                match cv {
                    CoordValue::Observed(lit) => {
                        out.insert(coord.clone(), lit);
                    }
                    CoordValue::Missing | CoordValue::Symbolic => {
                        missing_slots.push(if field.starts_with(&format!("{entity}.")) {
                            field.clone()
                        } else {
                            format!("{entity}.{field}")
                        });
                    }
                }
            }
            ShigureMemberCoordValue::Missing => {
                missing_slots.push(format!("{scope}.{coord}"));
            }
        }
    }
    Ok(out)
}

fn lower_single_origin(
    orig: &ShigureOriginRef,
    archmap: &CheckedArchMap,
    decl_name: &str,
    context: &str,
    origins: &mut BTreeSet<SourceRef>,
) -> Result<SourceRef, ValidationError> {
    let refs = lower_shigure_origin(orig, archmap, decl_name, context)?;
    let primary = refs
        .first()
        .cloned()
        .ok_or_else(|| conv_err(format!("empty origin refs in {context}")))?;
    for r in refs {
        origins.insert(r);
    }
    Ok(primary)
}

fn lower_matrix_rows(
    rows: &[Vec<ShigureMemberCoordValue>],
    archmap: &CheckedArchMap,
    snapshot_id: Option<&str>,
    coeff_domain: &CoeffDomain,
    fallback_ref: &SourceRef,
    label: &str,
    origins: &mut BTreeSet<SourceRef>,
) -> Result<Vec<Vec<ScalarLit>>, ValidationError> {
    let mut out = Vec::with_capacity(rows.len());
    for (r, row) in rows.iter().enumerate() {
        let mut lowered_row = Vec::with_capacity(row.len());
        for (c, cell) in row.iter().enumerate() {
            lowered_row.push(lower_required_scalar(
                cell,
                archmap,
                snapshot_id,
                coeff_domain,
                fallback_ref,
                &format!("{label}[{r}][{c}]"),
                origins,
            )?);
        }
        out.push(lowered_row);
    }
    Ok(out)
}

pub(super) fn convert_revision_task(
    inputs: &CheckedInputs,
    task_name: Option<&str>,
    snapshot_id: Option<&str>,
) -> Result<CheckedRevisionTask, ValidationError> {
    let shigure = inputs.law().shigure();
    if shigure.is_empty() {
        return Err(conv_err(
            "no `shigure` declarations found in CheckedLaw input",
        ));
    }
    let archmap = inputs.archmap();
    ensure_snapshot_exists(archmap, snapshot_id, "ShigureConverter::with_snapshot")?;

    let (_, decl) = select_named_decl(&shigure.revision_tasks, task_name, "shigure revision")?;
    let coeff_domain = lower_coeff_domain(&decl.coeff_domain);
    let (mut origins, primary_ref) =
        lower_p4_origins(&decl.origins, archmap, &decl.name, &decl.name)?;
    let mut missing_slots = Vec::new();

    let coords = lower_coords(&decl.coords, &coeff_domain, &decl.name)?;
    let shared_constraints =
        lower_constraints(&decl.shared_constraints, &coeff_domain, &decl.name)?;

    let before = RevisionSideSpec {
        assignments: lower_optional_assignments(
            &decl.before.assignments,
            archmap,
            snapshot_id,
            &coeff_domain,
            &primary_ref,
            &format!("{}.before", decl.name),
            &mut origins,
            &mut missing_slots,
        )?,
        extra_constraints: lower_constraints(
            &decl.before.extra_constraints,
            &coeff_domain,
            &format!("{}.before", decl.name),
        )?,
    };
    let after = RevisionSideSpec {
        assignments: lower_optional_assignments(
            &decl.after.assignments,
            archmap,
            snapshot_id,
            &coeff_domain,
            &primary_ref,
            &format!("{}.after", decl.name),
            &mut origins,
            &mut missing_slots,
        )?,
        extra_constraints: lower_constraints(
            &decl.after.extra_constraints,
            &coeff_domain,
            &format!("{}.after", decl.name),
        )?,
    };

    let mut probes = Vec::with_capacity(decl.probes.len());
    for p in &decl.probes {
        let p_ctx = format!("{}.probe.{}", decl.name, p.name);
        probes.push(RevisionEvalProbe {
            name: p.name.clone(),
            support: p.support.clone(),
            target_coord: p.target_coord.clone(),
            expected_value: lower_scalar_lit(&p.expected_value, &coeff_domain, &p_ctx)?,
            antecedent_coord: p.antecedent_coord.clone(),
            antecedent_value: p
                .antecedent_value
                .as_ref()
                .map(|av| lower_scalar_lit(av, &coeff_domain, &p_ctx))
                .transpose()?,
        });
    }

    let snf_spec = match &decl.snf {
        Some(snf) => {
            let snf_dom = lower_coeff_domain(&snf.coeff_domain);
            let (op_in_common_p0, m_before, m_after) = match &snf.operator {
                ShigureSnfOperatorMode::Common(rows) => {
                    let m = lower_matrix_rows(
                        rows,
                        archmap,
                        snapshot_id,
                        &snf_dom,
                        &primary_ref,
                        "revision.snf.common_operator",
                        &mut origins,
                    )?;
                    (true, m.clone(), m)
                }
                ShigureSnfOperatorMode::Split { before, after } => (
                    false,
                    lower_matrix_rows(
                        before,
                        archmap,
                        snapshot_id,
                        &snf_dom,
                        &primary_ref,
                        "revision.snf.operator_before",
                        &mut origins,
                    )?,
                    lower_matrix_rows(
                        after,
                        archmap,
                        snapshot_id,
                        &snf_dom,
                        &primary_ref,
                        "revision.snf.operator_after",
                        &mut origins,
                    )?,
                ),
            };
            let rhs_before = snf
                .rhs_before
                .iter()
                .enumerate()
                .map(|(i, v)| {
                    lower_required_scalar(
                        v,
                        archmap,
                        snapshot_id,
                        &snf_dom,
                        &primary_ref,
                        &format!("revision.snf.rhs_before[{i}]"),
                        &mut origins,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            let rhs_after = snf
                .rhs_after
                .iter()
                .enumerate()
                .map(|(i, v)| {
                    lower_required_scalar(
                        v,
                        archmap,
                        snapshot_id,
                        &snf_dom,
                        &primary_ref,
                        &format!("revision.snf.rhs_after[{i}]"),
                        &mut origins,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            Some(SnfRevisionSpec {
                coeff_domain: snf_dom,
                m_before,
                m_after,
                num_cols: snf.num_cols,
                rhs_before,
                rhs_after,
                op_in_common_p0,
                op_uniquely_determined: snf.operator_unobserved.is_empty(),
                force_reuse_existing_snf: snf.force_reuse_existing_snf,
                origin_label_only: snf.origin_label_only,
            })
        }
        None => None,
    };

    CheckedRevisionTask::validate(RevisionTaskSpec {
        name: decl.name.clone(),
        kind: match decl.kind {
            ShigureRevisionKind::Extension => RevisionKind::Extension,
            ShigureRevisionKind::Span => RevisionKind::Span,
        },
        coeff_domain,
        coords,
        shared_constraints,
        before,
        after,
        explicit_delta_coords: decl.explicit_delta_coords.clone(),
        probes,
        snf_spec,
        max_completions: decl.max_completions,
        provenance: Provenance::new(origins.into_iter().collect(), Vec::new()),
        undeclared_unobserved_slots: missing_slots,
    })
}

pub(super) fn convert_multisource_task(
    inputs: &CheckedInputs,
    task_name: Option<&str>,
    snapshot_id: Option<&str>,
) -> Result<CheckedMultisourceTask, ValidationError> {
    let shigure = inputs.law().shigure();
    if shigure.is_empty() {
        return Err(conv_err(
            "no `shigure` declarations found in CheckedLaw input",
        ));
    }
    let archmap = inputs.archmap();
    ensure_snapshot_exists(archmap, snapshot_id, "ShigureConverter::with_snapshot")?;

    let (_, decl) =
        select_named_decl(&shigure.multisource_tasks, task_name, "shigure multisource")?;
    let coeff_domain = lower_coeff_domain(&decl.coeff_domain);
    let (mut origins, primary_ref) =
        lower_p4_origins(&decl.origins, archmap, &decl.name, &decl.name)?;
    let mut missing_slots = Vec::new();

    let coords = lower_coords(&decl.coords, &coeff_domain, &decl.name)?;
    let background_constraints =
        lower_constraints(&decl.background_constraints, &coeff_domain, &decl.name)?;

    let mut sources = Vec::with_capacity(decl.sources.len());
    for src in &decl.sources {
        let src_ctx = format!("{}.source.{}", decl.name, src.source_id);
        let origin = lower_single_origin(&src.origin, archmap, &decl.name, &src_ctx, &mut origins)?;
        let assignments = lower_optional_assignments(
            &src.assignments,
            archmap,
            snapshot_id,
            &coeff_domain,
            &origin,
            &src_ctx,
            &mut origins,
            &mut missing_slots,
        )?;
        let mut forbidden_values = Vec::with_capacity(src.forbidden_values.len());
        for (c, v) in &src.forbidden_values {
            forbidden_values.push((
                c.clone(),
                lower_required_scalar(
                    v,
                    archmap,
                    snapshot_id,
                    &coeff_domain,
                    &origin,
                    &format!("{src_ctx}.forbidden.{c}"),
                    &mut origins,
                )?,
            ));
        }
        let extra_constraints = lower_constraints(&src.extra_constraints, &coeff_domain, &src_ctx)?;
        sources.push(SourcePresentationSpec {
            source_id: src.source_id.clone(),
            origin,
            assignments,
            forbidden_values,
            extra_constraints,
        });
    }

    let support_goal = match &decl.support_goal {
        Some(sg) => {
            let trusted_assignments = lower_optional_assignments(
                &sg.trusted_assignments,
                archmap,
                snapshot_id,
                &coeff_domain,
                &primary_ref,
                &format!("{}.support_goal.trusted", decl.name),
                &mut origins,
                &mut missing_slots,
            )?;
            let mut candidates = Vec::with_capacity(sg.candidates.len());
            for cand in &sg.candidates {
                let c_ctx = format!("{}.candidate.{}", decl.name, cand.id);
                let origin =
                    lower_single_origin(&cand.origin, archmap, &decl.name, &c_ctx, &mut origins)?;
                let value = lower_required_scalar(
                    &cand.value,
                    archmap,
                    snapshot_id,
                    &coeff_domain,
                    &origin,
                    &c_ctx,
                    &mut origins,
                )?;
                let cost = cand
                    .cost
                    .as_ref()
                    .map(|lit| match lit {
                        archsig_input::law::shigure::ShigureScalarLit::Int(_) => {
                            lower_scalar_lit(lit, &CoeffDomain::Z, &format!("{c_ctx}.cost"))
                        }
                        archsig_input::law::shigure::ShigureScalarLit::Rat { .. } => {
                            lower_scalar_lit(lit, &CoeffDomain::Q, &format!("{c_ctx}.cost"))
                        }
                        archsig_input::law::shigure::ShigureScalarLit::Fp { .. } => {
                            Err(conv_err(format!("{c_ctx}.cost cannot be Fp literal")))
                        }
                    })
                    .transpose()?;
                let verified_actual_value = match &cand.verified_actual_value {
                    Some(v) => Some(lower_required_scalar(
                        v,
                        archmap,
                        snapshot_id,
                        &coeff_domain,
                        &origin,
                        &format!("{c_ctx}.verified_actual"),
                        &mut origins,
                    )?),
                    None => None,
                };
                candidates.push(CandidateRecordSpec {
                    id: cand.id.clone(),
                    coord: cand.coord.clone(),
                    value,
                    cost,
                    origin,
                    verified_actual_value,
                });
            }
            let goal = match &sg.goal {
                ShigureSupportGoalFormula::CoordEquality(a, b) => {
                    SupportGoalFormula::CoordEquality(a.clone(), b.clone())
                }
                ShigureSupportGoalFormula::CoordEqualsConst(c, lit) => {
                    SupportGoalFormula::CoordEqualsConst(
                        c.clone(),
                        lower_scalar_lit(
                            lit,
                            &coeff_domain,
                            &format!("{}.support_goal", decl.name),
                        )?,
                    )
                }
            };
            Some(SupportGoalSpec {
                trusted_assignments,
                candidates,
                goal,
                expected_truth: sg.expected_truth,
                check_post_adoption_stability: sg.check_post_adoption_stability,
            })
        }
        None => None,
    };

    CheckedMultisourceTask::validate(MultisourceTaskSpec {
        name: decl.name.clone(),
        coeff_domain,
        coords,
        background_constraints,
        sources,
        support_goal,
        max_sources_subset_steps: decl.max_sources_subset_steps,
        max_results: decl.max_results,
        provenance: Provenance::new(origins.into_iter().collect(), Vec::new()),
        undeclared_unobserved_slots: missing_slots,
    })
}
