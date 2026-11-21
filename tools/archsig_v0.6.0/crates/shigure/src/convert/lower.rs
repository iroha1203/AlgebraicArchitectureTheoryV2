//! `CheckedInputs` から `CheckedShigureTask` への厳密な lowering 実装。

use super::lower_expr::{
    conv_err, harvest_archmap_origins, law_source_ref, lower_poly_expr, resolve_observed_coord,
};
use crate::ir::change::{
    ChangeSpec, EditableTarget, EvalCondition, FixedTarget, NamedPoly, ParamDecl, PointDomain,
};
use crate::ir::presentation::{
    ComparisonPair, CoordDecl, CoordValue, LawKind, ObservationDecl, OperationDecl, PhaseDecl,
    Presentation, SortDecl, StateComparison, StateLaw, TranslatedStep, TranslatedWord,
    WordTranslation,
};
use crate::ir::provenance::{Provenance, SourceRef};
use crate::ir::term::CoeffDomain;
use crate::ir::validate::{CheckedShigureTask, ValidationError};
use archsig_input::archmap::CheckedArchMap;
use archsig_input::input::CheckedInputs;
use archsig_input::law::shigure::{
    CheckedShigureDecls, ShigureChangeSpec, ShigureCoeffDomain, ShigureComparison,
    ShigureCoordBinding, ShigureEditableTarget, ShigureEvalCondition, ShigureFixedTarget,
    ShigureLawKind, ShigurePointDomain, ShigurePresentation,
};
use std::collections::{BTreeMap, BTreeSet};

struct SelectedTask<'a> {
    comparison: &'a ShigureComparison,
    change_spec: &'a ShigureChangeSpec,
    eval_condition: Option<&'a ShigureEvalCondition>,
}

pub(super) fn convert_checked_inputs(
    inputs: &CheckedInputs,
    task_name: Option<&str>,
    snapshot_id: Option<&str>,
) -> Result<CheckedShigureTask, ValidationError> {
    let shigure = inputs.law().shigure();
    if shigure.is_empty() {
        return Err(conv_err(
            "no `shigure` declarations found in CheckedLaw input",
        ));
    }

    let selected = select_task(shigure, task_name)?;
    let archmap = inputs.archmap();
    if let Some(sid) = snapshot_id
        && !archmap.snapshots().iter().any(|s| s.id == sid)
    {
        return Err(ValidationError::UnknownRef {
            kind: "snapshot",
            name: sid.to_owned(),
            context: "ShigureConverter::with_snapshot".to_owned(),
        });
    }

    let before_decl = shigure
        .presentations
        .get(&selected.comparison.before)
        .ok_or_else(|| ValidationError::UnknownRef {
            kind: "presentation",
            name: selected.comparison.before.clone(),
            context: selected.comparison.name.clone(),
        })?;
    let after_decl = shigure
        .presentations
        .get(&selected.comparison.after)
        .ok_or_else(|| ValidationError::UnknownRef {
            kind: "presentation",
            name: selected.comparison.after.clone(),
            context: selected.comparison.name.clone(),
        })?;

    let archmap_origins = harvest_archmap_origins(archmap, snapshot_id)?;
    let param_names: BTreeSet<String> = selected
        .change_spec
        .parameters
        .iter()
        .map(|p| p.name.clone())
        .collect();
    let empty_params = BTreeSet::new();

    // `before` 表示には探索パラメータを許可しない（パラメータが出現した場合は明示エラー）。
    let before = lower_presentation(
        before_decl,
        archmap,
        snapshot_id,
        &archmap_origins,
        &empty_params,
        Some(&param_names),
    )?;
    let after = lower_presentation(
        after_decl,
        archmap,
        snapshot_id,
        &archmap_origins,
        &param_names,
        None,
    )?;

    let pair = lower_comparison_pair(selected.comparison, before, after, &param_names)?;
    let change_spec = lower_change_spec(selected.change_spec, &archmap_origins);
    let eval_condition = selected
        .eval_condition
        .map(|ec| {
            lower_eval_condition(
                ec,
                &change_spec.coeff_domain,
                &param_names,
                &archmap_origins,
            )
        })
        .transpose()?;

    CheckedShigureTask::validate(pair, change_spec, eval_condition)
}

fn select_task<'a>(
    decls: &'a CheckedShigureDecls,
    task_name: Option<&str>,
) -> Result<SelectedTask<'a>, ValidationError> {
    if let Some(name) = task_name {
        let task = if let Some(exact) = decls.tasks.get(name) {
            exact
        } else {
            let suffix = format!(".{name}");
            let matches: Vec<_> = decls
                .tasks
                .iter()
                .filter(|(k, _)| k.ends_with(&suffix))
                .map(|(_, v)| v)
                .collect();
            match matches.as_slice() {
                [only] => *only,
                [] => {
                    return Err(ValidationError::UnknownRef {
                        kind: "shigure task",
                        name: name.to_owned(),
                        context: "ShigureConverter".to_owned(),
                    });
                }
                _ => {
                    return Err(conv_err(format!(
                        "ambiguous short task name `{name}`; specify full `Reading.Task` name"
                    )));
                }
            }
        };
        let comparison =
            decls
                .comparisons
                .get(&task.comparison)
                .ok_or_else(|| ValidationError::UnknownRef {
                    kind: "shigure comparison",
                    name: task.comparison.clone(),
                    context: task.name.clone(),
                })?;
        let change_spec = decls.change_specs.get(&task.change_spec).ok_or_else(|| {
            ValidationError::UnknownRef {
                kind: "shigure change_spec",
                name: task.change_spec.clone(),
                context: task.name.clone(),
            }
        })?;
        let eval_condition = task
            .eval_condition
            .as_ref()
            .map(|ec| {
                decls
                    .eval_conditions
                    .get(ec)
                    .ok_or_else(|| ValidationError::UnknownRef {
                        kind: "shigure eval_condition",
                        name: ec.clone(),
                        context: task.name.clone(),
                    })
            })
            .transpose()?;
        return Ok(SelectedTask {
            comparison,
            change_spec,
            eval_condition,
        });
    }

    if decls.tasks.len() == 1 {
        let task = decls.tasks.values().next().expect("len == 1");
        return select_task(decls, Some(&task.name));
    }
    if decls.tasks.len() > 1 {
        return Err(conv_err(format!(
            "multiple `shigure task` declarations exist ({}); specify a task name explicitly",
            decls.tasks.keys().cloned().collect::<Vec<_>>().join(", ")
        )));
    }

    // task 未宣言時は comparison / change_spec が各 1 件・eval_condition が 0..=1 件のときのみ一意選択。
    if decls.comparisons.len() != 1
        || decls.change_specs.len() != 1
        || decls.eval_conditions.len() > 1
    {
        return Err(conv_err(
            "cannot infer a unique SHIGURE task without an explicit `shigure task` declaration",
        ));
    }
    Ok(SelectedTask {
        comparison: decls.comparisons.values().next().expect("len == 1"),
        change_spec: decls.change_specs.values().next().expect("len == 1"),
        eval_condition: decls.eval_conditions.values().next(),
    })
}

fn lower_coeff_domain(d: &ShigureCoeffDomain) -> CoeffDomain {
    match d {
        ShigureCoeffDomain::Z => CoeffDomain::Z,
        ShigureCoeffDomain::Q => CoeffDomain::Q,
        ShigureCoeffDomain::Fp(p) => CoeffDomain::Fp(p.clone()),
    }
}

fn lower_point_domain(d: &ShigurePointDomain) -> PointDomain {
    match d {
        ShigurePointDomain::AlgebraicClosure => PointDomain::AlgebraicClosure,
        ShigurePointDomain::RationalPoints => PointDomain::RationalPoints,
        ShigurePointDomain::IntegerPoints => PointDomain::IntegerPoints,
        ShigurePointDomain::FiniteFieldPoints(p) => PointDomain::FiniteFieldPoints(p.clone()),
        ShigurePointDomain::UniversalRing => PointDomain::UniversalRing,
    }
}

fn lower_law_kind(k: ShigureLawKind) -> LawKind {
    match k {
        ShigureLawKind::Semantic => LawKind::Semantic,
        ShigureLawKind::Representation => LawKind::Representation,
    }
}

fn lower_presentation(
    decl: &ShigurePresentation,
    archmap: &CheckedArchMap,
    snapshot_id: Option<&str>,
    archmap_origins: &[SourceRef],
    allowed_params: &BTreeSet<String>,
    forbidden_params: Option<&BTreeSet<String>>,
) -> Result<Presentation, ValidationError> {
    let coeff_domain = lower_coeff_domain(&decl.coeff_domain);
    let pres_ref = law_source_ref(&decl.name);

    let sorts: Vec<SortDecl> = decl
        .sorts
        .iter()
        .map(|s| SortDecl {
            name: s.name.clone(),
            rank: s.rank,
            coeff_domain: coeff_domain.clone(),
            provenance: Some(pres_ref.clone()),
        })
        .collect();

    let mut phases = Vec::with_capacity(decl.phases.len());
    let mut phase_coord_sets: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for ph in &decl.phases {
        let mut coords = Vec::with_capacity(ph.coords.len());
        let mut coord_set = BTreeSet::new();
        for c in &ph.coords {
            coord_set.insert(c.name.clone());
            let (value, provenance) = match &c.binding {
                ShigureCoordBinding::Symbolic => (CoordValue::Symbolic, Some(pres_ref.clone())),
                ShigureCoordBinding::ObservedField { entity, field, .. } => resolve_observed_coord(
                    archmap,
                    snapshot_id,
                    entity,
                    field,
                    &coeff_domain,
                    &pres_ref,
                )?,
            };
            coords.push(CoordDecl {
                name: c.name.clone(),
                sort: c.sort.clone(),
                value,
                provenance,
            });
        }
        let empty_args = BTreeSet::new();
        let mut state_laws = Vec::with_capacity(ph.state_laws.len());
        for l in &ph.state_laws {
            let ctx = format!("{}.{}.{}", decl.name, ph.name, l.name);
            let polynomial = lower_poly_expr(
                &l.expr,
                &coeff_domain,
                &coord_set,
                &empty_args,
                allowed_params,
                forbidden_params,
                &ctx,
            )?;
            state_laws.push(StateLaw {
                name: l.name.clone(),
                kind: lower_law_kind(l.kind),
                polynomial,
                provenance: Some(pres_ref.clone()),
            });
        }
        phase_coord_sets.insert(ph.name.clone(), coord_set);
        phases.push(PhaseDecl {
            name: ph.name.clone(),
            coords,
            state_laws,
            provenance: Some(pres_ref.clone()),
        });
    }

    let mut operations = Vec::with_capacity(decl.operations.len());
    for op in &decl.operations {
        let src_coords =
            phase_coord_sets
                .get(&op.source_phase)
                .ok_or_else(|| ValidationError::UnknownRef {
                    kind: "phase",
                    name: op.source_phase.clone(),
                    context: format!("{}.{}", decl.name, op.name),
                })?;
        let arg_set: BTreeSet<String> = op.args.iter().map(|(a, _)| a.clone()).collect();
        let mut updates = BTreeMap::new();
        for (coord, expr) in &op.updates {
            let ctx = format!("{}.{}.{coord}", decl.name, op.name);
            let lowered = lower_poly_expr(
                expr,
                &coeff_domain,
                src_coords,
                &arg_set,
                allowed_params,
                forbidden_params,
                &ctx,
            )?;
            updates.insert(coord.clone(), lowered);
        }
        operations.push(OperationDecl {
            name: op.name.clone(),
            source_phase: op.source_phase.clone(),
            target_phase: op.target_phase.clone(),
            args: op.args.clone(),
            updates,
            provenance: Some(pres_ref.clone()),
        });
    }

    let empty_args = BTreeSet::new();
    let mut observations = Vec::with_capacity(decl.observations.len());
    for obs in &decl.observations {
        let ph_coords =
            phase_coord_sets
                .get(&obs.phase)
                .ok_or_else(|| ValidationError::UnknownRef {
                    kind: "phase",
                    name: obs.phase.clone(),
                    context: format!("{}.{}", decl.name, obs.name),
                })?;
        let ctx = format!("{}.{}.{}", decl.name, obs.phase, obs.name);
        let mut components = Vec::with_capacity(obs.components.len());
        for comp in &obs.components {
            components.push(lower_poly_expr(
                comp,
                &coeff_domain,
                ph_coords,
                &empty_args,
                allowed_params,
                forbidden_params,
                &ctx,
            )?);
        }
        observations.push(ObservationDecl {
            name: obs.name.clone(),
            phase: obs.phase.clone(),
            components,
            provenance: Some(pres_ref.clone()),
        });
    }

    let mut origins = vec![pres_ref];
    origins.extend(archmap_origins.iter().cloned());

    Ok(Presentation {
        name: decl.name.clone(),
        coeff_domain,
        sorts,
        phases,
        operations,
        observations,
        provenance: Provenance {
            origins,
            clauses: vec![],
        },
    })
}

fn lower_comparison_pair(
    decl: &ShigureComparison,
    before: Presentation,
    after: Presentation,
    param_names: &BTreeSet<String>,
) -> Result<ComparisonPair, ValidationError> {
    let cmp_ref = law_source_ref(&decl.name);
    let domain = after.coeff_domain.clone();
    let empty_args = BTreeSet::new();

    let mut state_comparisons = Vec::with_capacity(decl.state_comparisons.len());
    for sc in &decl.state_comparisons {
        let after_ph = after
            .phase(&sc.after_phase)
            .ok_or_else(|| ValidationError::UnknownRef {
                kind: "after phase",
                name: sc.after_phase.clone(),
                context: decl.name.clone(),
            })?;
        let state_vars: BTreeSet<String> = after_ph.coords.iter().map(|c| c.name.clone()).collect();
        let mut map = BTreeMap::new();
        for (coord, expr) in &sc.map {
            let ctx = format!("{}.state_map.{}.{coord}", decl.name, sc.after_phase);
            let lowered = lower_poly_expr(
                expr,
                &domain,
                &state_vars,
                &empty_args,
                param_names,
                None,
                &ctx,
            )?;
            map.insert(coord.clone(), lowered);
        }
        state_comparisons.push(StateComparison {
            after_phase: sc.after_phase.clone(),
            before_phase: sc.before_phase.clone(),
            map,
            provenance: Some(cmp_ref.clone()),
        });
    }

    let mut entries = Vec::with_capacity(decl.word_translation.len());
    for tw in &decl.word_translation {
        let after_op =
            after
                .operation(&tw.after_operation)
                .ok_or_else(|| ValidationError::UnknownRef {
                    kind: "after operation",
                    name: tw.after_operation.clone(),
                    context: decl.name.clone(),
                })?;
        let src_ph =
            after
                .phase(&after_op.source_phase)
                .ok_or_else(|| ValidationError::UnknownRef {
                    kind: "after phase",
                    name: after_op.source_phase.clone(),
                    context: decl.name.clone(),
                })?;
        let state_vars: BTreeSet<String> = src_ph.coords.iter().map(|c| c.name.clone()).collect();
        let arg_vars: BTreeSet<String> = after_op.args.iter().map(|(a, _)| a.clone()).collect();
        let mut steps = Vec::with_capacity(tw.steps.len());
        for st in &tw.steps {
            let mut arg_exprs = Vec::with_capacity(st.arg_exprs.len());
            for (idx, expr) in st.arg_exprs.iter().enumerate() {
                let ctx = format!(
                    "{}.translate.{}.{}[{idx}]",
                    decl.name, tw.after_operation, st.before_operation
                );
                arg_exprs.push(lower_poly_expr(
                    expr,
                    &domain,
                    &state_vars,
                    &arg_vars,
                    param_names,
                    None,
                    &ctx,
                )?);
            }
            steps.push(TranslatedStep {
                before_operation: st.before_operation.clone(),
                arg_exprs,
            });
        }
        entries.push(TranslatedWord {
            after_operation: tw.after_operation.clone(),
            steps,
            provenance: Some(cmp_ref.clone()),
        });
    }

    Ok(ComparisonPair {
        before,
        after,
        state_comparisons,
        word_translation: WordTranslation { entries },
    })
}

fn lower_change_spec(decl: &ShigureChangeSpec, archmap_origins: &[SourceRef]) -> ChangeSpec {
    let spec_ref = law_source_ref(&decl.name);
    let parameters = decl
        .parameters
        .iter()
        .map(|p| ParamDecl {
            name: p.name.clone(),
            coeff_domain: lower_coeff_domain(&p.coeff_domain),
            provenance: Some(spec_ref.clone()),
        })
        .collect();
    let fixed = decl
        .fixed
        .iter()
        .map(|(t, _)| match t {
            ShigureFixedTarget::SemanticLaw {
                presentation,
                phase,
                law,
            } => FixedTarget::SemanticLaw {
                presentation: presentation.clone(),
                phase: phase.clone(),
                law: law.clone(),
            },
            ShigureFixedTarget::RepresentationLaw {
                presentation,
                phase,
                law,
            } => FixedTarget::RepresentationLaw {
                presentation: presentation.clone(),
                phase: phase.clone(),
                law: law.clone(),
            },
            ShigureFixedTarget::OperationExpr {
                presentation,
                operation,
            } => FixedTarget::OperationExpr {
                presentation: presentation.clone(),
                operation: operation.clone(),
            },
            ShigureFixedTarget::ObservationExpr {
                presentation,
                phase,
                observation,
            } => FixedTarget::ObservationExpr {
                presentation: presentation.clone(),
                phase: phase.clone(),
                observation: observation.clone(),
            },
            ShigureFixedTarget::StateComparisonExpr { after_phase } => {
                FixedTarget::StateComparisonExpr {
                    after_phase: after_phase.clone(),
                }
            }
            ShigureFixedTarget::WordTranslationOp { operation } => FixedTarget::WordTranslationOp {
                operation: operation.clone(),
            },
        })
        .collect();
    let editable = decl
        .editable
        .iter()
        .map(|(t, _)| match t {
            ShigureEditableTarget::OperationExpr {
                presentation,
                operation,
            } => EditableTarget::OperationExpr {
                presentation: presentation.clone(),
                operation: operation.clone(),
            },
            ShigureEditableTarget::RepresentationLaw {
                presentation,
                phase,
                law,
            } => EditableTarget::RepresentationLaw {
                presentation: presentation.clone(),
                phase: phase.clone(),
                law: law.clone(),
            },
            ShigureEditableTarget::StateComparisonExpr { after_phase } => {
                EditableTarget::StateComparisonExpr {
                    after_phase: after_phase.clone(),
                }
            }
        })
        .collect();
    let mut origins = vec![spec_ref];
    origins.extend(archmap_origins.iter().cloned());
    ChangeSpec {
        name: decl.name.clone(),
        coeff_domain: lower_coeff_domain(&decl.coeff_domain),
        parameters,
        fixed,
        editable,
        provenance: Provenance {
            origins,
            clauses: vec![],
        },
    }
}

fn lower_eval_condition(
    decl: &ShigureEvalCondition,
    coeff_domain: &CoeffDomain,
    param_names: &BTreeSet<String>,
    archmap_origins: &[SourceRef],
) -> Result<EvalCondition, ValidationError> {
    let ec_ref = law_source_ref(&decl.name);
    let empty = BTreeSet::new();
    let lower_named = |items: &[archsig_input::law::shigure::ShigureNamedPoly],
                       kind: &str|
     -> Result<Vec<NamedPoly>, ValidationError> {
        let mut out = Vec::with_capacity(items.len());
        for item in items {
            let ctx = format!("{}.{kind}.{}", decl.name, item.name);
            let expr = lower_poly_expr(
                &item.expr,
                coeff_domain,
                &empty,
                &empty,
                param_names,
                None,
                &ctx,
            )?;
            out.push(NamedPoly {
                name: item.name.clone(),
                expr,
                provenance: Some(ec_ref.clone()),
            });
        }
        Ok(out)
    };
    let evaluations = lower_named(&decl.evaluations, "eval")?;
    let equations = lower_named(&decl.equations, "equation")?;
    let invertibles = lower_named(&decl.invertibles, "invertible")?;
    let mut origins = vec![ec_ref];
    origins.extend(archmap_origins.iter().cloned());
    Ok(EvalCondition {
        name: decl.name.clone(),
        evaluations,
        equations,
        invertibles,
        point_domain: lower_point_domain(&decl.point_domain),
        provenance: Provenance {
            origins,
            clauses: vec![],
        },
    })
}
