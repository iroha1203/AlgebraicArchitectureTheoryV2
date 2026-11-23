//! `shigure diagram`・`shigure path`・`shigure transfer` のスコープ付き `change_spec` 検査ヘルパ。

use super::check::CResult;
use super::*;
use crate::law::ast::Span;
use crate::law::check::reference;
use archsig_common::control::{Checkpoint, Control};
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;
use std::collections::BTreeMap;

pub(super) struct ScopedMorphismMeta<'a> {
    pub sc_after_phases: Vec<&'a str>,
    pub wt_after_ops: Vec<&'a str>,
    pub is_fixed: bool,
}

impl<'a> ScopedMorphismMeta<'a> {
    pub(super) fn from_body(
        body: &'a ShigureMorphismBody,
        src_pres: &'a ShigurePresentation,
        decls: &'a CheckedShigureDecls,
        is_fixed: bool,
    ) -> Self {
        match body {
            ShigureMorphismBody::Comparison(name) => {
                let cmp = &decls.comparisons[name];
                Self {
                    sc_after_phases: cmp
                        .state_comparisons
                        .iter()
                        .map(|s| s.after_phase.as_str())
                        .collect(),
                    wt_after_ops: cmp
                        .word_translation
                        .iter()
                        .map(|w| w.after_operation.as_str())
                        .collect(),
                    is_fixed,
                }
            }
            ShigureMorphismBody::Identity => Self {
                sc_after_phases: src_pres.phases.iter().map(|p| p.name.as_str()).collect(),
                wt_after_ops: src_pres
                    .operations
                    .iter()
                    .map(|o| o.name.as_str())
                    .collect(),
                is_fixed,
            },
            ShigureMorphismBody::Inline {
                state_comparisons,
                word_translation,
            } => Self {
                sc_after_phases: state_comparisons
                    .iter()
                    .map(|s| s.after_phase.as_str())
                    .collect(),
                wt_after_ops: word_translation
                    .iter()
                    .map(|w| w.after_operation.as_str())
                    .collect(),
                is_fixed,
            },
        }
    }
}

fn scoped_pres<'a, E: InputError>(
    pres_map: &'a BTreeMap<&str, Vec<(&'a ShigurePresentation, bool)>>,
    presentation: &str,
    span: Span,
    kind: &str,
    label: &str,
) -> CResult<&'a [(&'a ShigurePresentation, bool)], E> {
    match pres_map.get(presentation) {
        Some(vs) => Ok(vs.as_slice()),
        None => reference(
            span,
            format!("{kind} target references presentation `{presentation}` outside {label}"),
        ),
    }
}

pub(super) fn check_scoped_change_spec_targets<E: InputError>(
    spec: &ShigureChangeSpec,
    pres_map: &BTreeMap<&str, Vec<(&ShigurePresentation, bool)>>,
    morphs: &[ScopedMorphismMeta<'_>],
    label: &str,
    control: &Control,
) -> CResult<(), E> {
    for (target, span) in &spec.fixed {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        match target {
            ShigureFixedTarget::SemanticLaw {
                presentation,
                phase,
                law,
            }
            | ShigureFixedTarget::RepresentationLaw {
                presentation,
                phase,
                law,
            } => {
                let vs = scoped_pres(pres_map, presentation, *span, "fixed", label)?;
                if !vs.iter().any(|(p, _)| {
                    p.phases
                        .iter()
                        .find(|ph| ph.name == *phase)
                        .is_some_and(|ph| ph.state_laws.iter().any(|l| l.name == *law))
                }) {
                    return reference(
                        *span,
                        format!("unknown state law `{presentation}.{phase}.{law}` in {label}"),
                    );
                }
            }
            ShigureFixedTarget::OperationExpr {
                presentation,
                operation,
            } => {
                let vs = scoped_pres(pres_map, presentation, *span, "fixed", label)?;
                if !vs
                    .iter()
                    .any(|(p, _)| p.operations.iter().any(|o| o.name == *operation))
                {
                    return reference(
                        *span,
                        format!("unknown operation `{presentation}.{operation}` in {label}"),
                    );
                }
            }
            ShigureFixedTarget::ObservationExpr {
                presentation,
                phase,
                observation,
            } => {
                let vs = scoped_pres(pres_map, presentation, *span, "fixed", label)?;
                if !vs.iter().any(|(p, _)| {
                    p.observations
                        .iter()
                        .any(|o| o.phase == *phase && o.name == *observation)
                }) {
                    return reference(
                        *span,
                        format!(
                            "unknown observation `{presentation}.{phase}.{observation}` in {label}"
                        ),
                    );
                }
            }
            ShigureFixedTarget::StateComparisonExpr { after_phase } => {
                if !morphs
                    .iter()
                    .any(|m| m.sc_after_phases.contains(&after_phase.as_str()))
                {
                    return reference(
                        *span,
                        format!("fixed state_comparison `{after_phase}` not found in {label}"),
                    );
                }
            }
            ShigureFixedTarget::WordTranslationOp { operation } => {
                if !morphs
                    .iter()
                    .any(|m| m.wt_after_ops.contains(&operation.as_str()))
                {
                    return reference(
                        *span,
                        format!("fixed word_translation `{operation}` not found in {label}"),
                    );
                }
            }
        }
    }

    for (target, span) in &spec.editable {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        match target {
            ShigureEditableTarget::OperationExpr {
                presentation,
                operation,
            } => {
                let vs = scoped_pres(pres_map, presentation, *span, "editable", label)?;
                if !vs
                    .iter()
                    .any(|(p, _)| p.operations.iter().any(|o| o.name == *operation))
                {
                    return reference(
                        *span,
                        format!("unknown operation `{presentation}.{operation}` in {label}"),
                    );
                }
                if vs.iter().any(|(_, is_fixed)| *is_fixed) {
                    return Err(Box::new(Issue::law(
                        Code::Type,
                        *span,
                        format!(
                            "editable target `{presentation}.{operation}` cannot belong to a fixed vertex"
                        ),
                    ))
                    .into());
                }
            }
            ShigureEditableTarget::RepresentationLaw {
                presentation,
                phase,
                law,
            } => {
                let vs = scoped_pres(pres_map, presentation, *span, "editable", label)?;
                if !vs.iter().any(|(p, _)| {
                    p.phases
                        .iter()
                        .find(|ph| ph.name == *phase)
                        .is_some_and(|ph| ph.state_laws.iter().any(|l| l.name == *law))
                }) {
                    return reference(
                        *span,
                        format!(
                            "unknown representation_law `{presentation}.{phase}.{law}` in {label}"
                        ),
                    );
                }
                if vs.iter().any(|(_, is_fixed)| *is_fixed) {
                    return Err(Box::new(Issue::law(
                        Code::Type,
                        *span,
                        format!(
                            "editable target `{presentation}.{phase}.{law}` cannot belong to a fixed vertex"
                        ),
                    ))
                    .into());
                }
            }
            ShigureEditableTarget::StateComparisonExpr { after_phase } => {
                let any_exists = morphs
                    .iter()
                    .any(|m| m.sc_after_phases.contains(&after_phase.as_str()));
                if !any_exists {
                    return reference(
                        *span,
                        format!("editable state_comparison `{after_phase}` not found in {label}"),
                    );
                }
                let editable_exists = morphs
                    .iter()
                    .any(|m| !m.is_fixed && m.sc_after_phases.contains(&after_phase.as_str()));
                if !editable_exists {
                    return Err(Box::new(Issue::law(
                        Code::Type,
                        *span,
                        format!(
                            "editable state_comparison `{after_phase}` cannot belong only to fixed edges"
                        ),
                    ))
                    .into());
                }
            }
        }
    }
    Ok(())
}
