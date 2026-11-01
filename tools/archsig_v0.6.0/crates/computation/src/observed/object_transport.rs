//! 対象読取り間の参照束縛と、元の型付き評価の照合。
use super::object_evaluate::{ObjectEvaluation, ObjectEvaluationOutcome};
use crate::construction::{
    ConstructionFailure,
    maps::{ConfigurationTransport, DeclarationPair},
    readings::{ObjectInstance, ObjectReadingInstances},
};
use archsig_common::control::{Checkpoint, Control};
use archsig_input::archmap::Fact as FactPointer;
pub(super) struct MappedInstance {
    pub index: Option<usize>,
    pub bindings: Vec<(String, FactPointer)>,
}
pub(super) fn mapped_instance(
    objects: &ConfigurationTransport,
    source: &ObjectInstance,
    pair: &DeclarationPair,
    target: &ObjectReadingInstances,
    c: &Control,
    point: Checkpoint,
) -> Result<MappedInstance, ConstructionFailure> {
    let mut bindings = Vec::new();
    for b in source.bindings() {
        c.checkpoint(point)?;
        let parameter = pair
            .parameters()
            .iter()
            .find(|(name, _)| name == &b.parameter().name)
            .ok_or_else(|| ConstructionFailure::Inconsistent(internal!("対応parameterがない")))?;
        let f = b.subject();
        let image = if objects.action().source_configuration().family().contains(f) {
            objects
                .action()
                .image(f)
                .ok_or_else(|| ConstructionFailure::Inconsistent(internal!("参照束縛の像がない")))?
        } else {
            f
        };
        bindings.push((parameter.1.clone(), image.clone()));
    }
    for (index, row) in target.instances().iter().enumerate() {
        c.checkpoint(point)?;
        if row.declaration().name == pair.target()
            && row.bindings().len() == bindings.len()
            && row.bindings().iter().all(|b| {
                bindings
                    .iter()
                    .any(|(name, f)| name == &b.parameter().name && f == b.subject())
            })
        {
            return Ok(MappedInstance {
                index: Some(index),
                bindings,
            });
        }
    }
    Ok(MappedInstance {
        index: None,
        bindings,
    })
}

pub(super) fn same_evaluation(a: Option<&ObjectEvaluation>, b: Option<&ObjectEvaluation>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(a), Some(b))
            if a.readings() == b.readings()
                && a.object() == b.object()
                && a.instance() == b.instance() =>
        {
            match (a.outcome(), b.outcome()) {
                (
                    ObjectEvaluationOutcome::NotApplicable,
                    ObjectEvaluationOutcome::NotApplicable,
                ) => true,
                (
                    ObjectEvaluationOutcome::Conditional(a),
                    ObjectEvaluationOutcome::Conditional(b),
                ) => a == b,
                (ObjectEvaluationOutcome::Evaluated(a), ObjectEvaluationOutcome::Evaluated(b)) => {
                    a.nodes == b.nodes
                        && a.answers == b.answers
                        && a.issues == b.issues
                        && a.status == b.status
                        && a.prepared().inputs().sources() == b.prepared().inputs().sources()
                        && a.prepared().requests().requests() == b.prepared().requests().requests()
                        && a.prepared().object_identity() == b.prepared().object_identity()
                        && a.prepared().object_instance() == b.prepared().object_instance()
                }
                (
                    ObjectEvaluationOutcome::FiniteView(a),
                    ObjectEvaluationOutcome::FiniteView(b),
                ) => super::object_view_family::same_family(a, b),
                _ => false,
            }
        }
        _ => false,
    }
}

pub(super) fn same_evaluation_controlled(
    a: Option<&ObjectEvaluation>,
    b: Option<&ObjectEvaluation>,
    c: &Control,
) -> Result<bool, ConstructionFailure> {
    c.checkpoint(Checkpoint::ObjectViewTransportFamily)?;
    match (a, b) {
        (Some(a), Some(b)) if a.same_origin(b) => match (a.outcome(), b.outcome()) {
            (ObjectEvaluationOutcome::FiniteView(a), ObjectEvaluationOutcome::FiniteView(b)) => {
                super::object_view_family::same_family_checked(a, b, c).map_err(|failure| {
                    match failure {
                        super::result::ValidationFailure::Stop(reason) => {
                            ConstructionFailure::Stopped(reason)
                        }
                        other => ConstructionFailure::Inconsistent(
                            other.internal_context(format!("view族の再照合: {other:?}")),
                        ),
                    }
                })
            }
            _ => Ok(same_evaluation(Some(a), Some(b))),
        },
        _ => Ok(same_evaluation(a, b)),
    }
}
