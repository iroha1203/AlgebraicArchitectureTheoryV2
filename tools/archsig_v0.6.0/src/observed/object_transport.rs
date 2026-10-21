//! 対象読取り間の参照束縛と、元の型付き評価の照合。
use super::{
    control::{Checkpoint, Control},
    object_evaluate::{ObjectEvaluation, ObjectEvaluationOutcome},
};
use crate::construction::{
    ConstructionFailure, FactPointer,
    maps::{ConfigurationTransport, DeclarationPair},
    readings::{ObjectInstance, ObjectReadingInstances},
};
pub(super) struct MappedInstance {
    pub index: Option<usize>,
    pub bindings: Vec<(String, FactPointer)>,
}
pub(super) fn mapped_instance(
    objects: &ConfigurationTransport,
    source: &ObjectInstance,
    pair: &DeclarationPair,
    target: &ObjectReadingInstances,
    c: &mut Control,
    point: Checkpoint,
) -> Result<MappedInstance, ConstructionFailure> {
    let mut bindings = Vec::new();
    for b in source.bindings() {
        c.checkpoint(point)?;
        let parameter = pair
            .parameters()
            .iter()
            .find(|(name, _)| name == &b.parameter().name)
            .ok_or_else(|| ConstructionFailure::Inconsistent("対応parameterがない".into()))?;
        let f = b.subject();
        let image = if objects.action().source_configuration().family().contains(f) {
            objects
                .action()
                .image(f)
                .ok_or_else(|| ConstructionFailure::Inconsistent("参照束縛の像がない".into()))?
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
                        && b.nodes == a.nodes
                        && a.answers == b.answers
                        && a.issues == b.issues
                        && a.status == b.status
                        && a.prepared().inputs().sources() == b.prepared().inputs().sources()
                        && a.prepared().requests().requests() == b.prepared().requests().requests()
                        && a.prepared().object_identity() == b.prepared().object_identity()
                        && a.prepared().object_instance() == b.prepared().object_instance()
                }
                _ => false,
            }
        }
        _ => false,
    }
}
