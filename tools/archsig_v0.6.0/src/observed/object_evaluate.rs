//! 対象から生成した参照域を、同じ型付き評価・再検査の環境へ渡す。
use super::{
    control::{Checkpoint, Control},
    input::CheckedInputs,
    result::*,
    *,
};
use crate::{
    construction::{
        ConstructionFailure, FactPointer,
        maps::ObjectIdentity,
        readings::{
            InstanceApplication, MembershipCondition, ObjectInstance, ObjectReadingInstances,
        },
    },
    types::Type,
};
use std::{collections::BTreeSet, sync::Arc};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ObjectContext {
    pub identity: ObjectIdentity,
    pub instance: ObjectInstance,
    local_types: BTreeSet<String>,
    known: Vec<FactPointer>,
    conditional: Vec<(String, FactPointer, FactPointer)>,
}
impl ObjectContext {
    pub(super) fn is_local(&self, ty: &Type) -> bool {
        matches!(ty, Type::Ref(entity) | Type::Owned(entity, _) if self.local_types.contains(entity))
    }

    pub(super) fn membership_subject(&self, subject: &crate::archmap::Subject) -> bool {
        self.local_types.contains(&subject.ty)
            && (self.identity.subject() == self.identity.root()
                || (subject.snapshot == self.identity.subject().snapshot
                    && subject.id == self.identity.subject().subject))
    }
    /// 直接の参照binderだけを対象域へ制限する。複合値域の参照leafは全型域のまま。
    pub(super) fn restrict(
        &self,
        ty: &Type,
        values: &mut Option<Vec<Scalar>>,
        missing: &mut Vec<Fact>,
        support: &mut Vec<Fact>,
        scope: &mut Scope,
        control: &Control,
        completions: &[(Fact, NodeRef, Scalar)],
    ) -> Result<(), ValidationFailure> {
        let (Type::Ref(entity) | Type::Owned(entity, _)) = ty else {
            return Ok(());
        };
        if !self.local_types.contains(entity) {
            return Ok(());
        }
        control.clone().checkpoint(Checkpoint::ObjectEvaluation)?;
        let mut allowed = self.known.clone();
        for (actual, subject, slot) in &self.conditional {
            control.clone().checkpoint(Checkpoint::ObjectEvaluation)?;
            if actual != entity {
                continue;
            }
            if let Some((_, _, value)) = completions.iter().find(|(f, _, _)| f == slot) {
                let Scalar::Subject {
                    snapshot,
                    subject: owner,
                    ..
                } = value
                else {
                    return Err("補完したownerが参照でない".into());
                };
                let root = self.identity.root();
                if snapshot == &root.snapshot && owner == &root.subject {
                    allowed.push(subject.clone());
                }
            } else {
                missing.push(slot.clone());
            }
        }
        // 所属を問う元slotも、選択部分対象の外ならこの量化の欠測ではない。
        missing.retain(|f| {
            self.known
                .iter()
                .any(|p| p.snapshot == f.snapshot && p.subject == f.subject)
                || self
                    .conditional
                    .iter()
                    .any(|(_, p, _)| p.snapshot == f.snapshot && p.subject == f.subject)
        });
        if let Some(values) = values {
            let mut restricted = Vec::new();
            for value in values.drain(..) {
                control.clone().checkpoint(Checkpoint::ObjectEvaluation)?;
                let Scalar::Subject {
                    snapshot,
                    subject,
                    entity: actual,
                } = &value
                else {
                    return Err("対象量化の元が参照でない".into());
                };
                if actual != entity {
                    return Err("対象量化の元型が違う".into());
                }
                if allowed
                    .iter()
                    .any(|p| &p.snapshot == snapshot && &p.subject == subject)
                {
                    restricted.push(value);
                }
            }
            *values = restricted;
        }
        missing.sort();
        missing.dedup();
        if !missing.is_empty() {
            *values = None;
            scope.completions = true;
        }
        scope.readings.insert(self.identity.reading().into());
        for fact in &allowed {
            control.clone().checkpoint(Checkpoint::ObjectEvaluation)?;
            scope.snapshots.insert(fact.snapshot.clone());
            support.push(fact.clone());
        }
        support.sort();
        support.dedup();
        control.clone().checkpoint(Checkpoint::ObjectEvaluation)?;
        Ok(())
    }
}

#[derive(Debug)]
pub enum ObjectEvaluationFailure {
    Construction(ConstructionFailure),
    Evaluation(Box<EvaluationFailure>),
    /// 通常のview要求が全束縛を要することを、入力不正や数学的未決へ読み替えない。
    NotImplemented {
        object: ObjectIdentity,
        instance: ObjectInstance,
    },
}
impl From<ConstructionFailure> for ObjectEvaluationFailure {
    fn from(f: ConstructionFailure) -> Self {
        Self::Construction(f)
    }
}
#[derive(Debug)]
pub enum ObjectEvaluationOutcome {
    NotApplicable,
    Conditional(Vec<MembershipCondition>),
    Evaluated(Box<ObservedEvaluation>),
}
/// 適用状態と、その対象の元宣言・束縛・型付き評価。全域延長の成立とは区別する。
#[derive(Debug)]
pub struct ObjectEvaluation {
    readings: ObjectReadingInstances,
    object: usize,
    instance: usize,
    outcome: ObjectEvaluationOutcome,
}
impl ObjectEvaluation {
    pub fn readings(&self) -> &ObjectReadingInstances {
        &self.readings
    }
    pub fn object(&self) -> &ObjectIdentity {
        self.readings.objects()[self.object].identity()
    }
    pub fn instance(&self) -> &ObjectInstance {
        &self.readings.instances()[self.instance]
    }
    pub fn outcome(&self) -> &ObjectEvaluationOutcome {
        &self.outcome
    }
}

pub fn evaluate_object_instance(
    inputs: Arc<CheckedInputs>,
    readings: &ObjectReadingInstances,
    object: usize,
    instance: usize,
    control: &mut Control,
) -> Result<ObjectEvaluation, ObjectEvaluationFailure> {
    control
        .checkpoint(Checkpoint::ObjectEvaluation)
        .map_err(ConstructionFailure::from)?;
    readings.recheck(&inputs, control)?;
    let selected = readings
        .objects()
        .get(object)
        .ok_or_else(|| ConstructionFailure::InvalidSelection("対象の添字がない".into()))?;
    let row = readings
        .instances()
        .get(instance)
        .ok_or_else(|| ConstructionFailure::InvalidSelection("instanceの添字がない".into()))?;
    let application = row
        .applications()
        .get(object)
        .ok_or_else(|| ConstructionFailure::Inconsistent("対象別適用の行がない".into()))?;
    let outcome = match application {
        InstanceApplication::NotApplicable => ObjectEvaluationOutcome::NotApplicable,
        InstanceApplication::Applicable { conditions } if !conditions.is_empty() => {
            ObjectEvaluationOutcome::Conditional(conditions.clone())
        }
        InstanceApplication::Applicable { .. } => {
            if row.declaration().kind == "view" && !row.parameters().is_empty() {
                return Err(ObjectEvaluationFailure::NotImplemented {
                    object: selected.identity().clone(),
                    instance: row.clone(),
                });
            }
            let c = readings.construction();
            let root = c.root();
            let local_types = readings.local_types().clone();
            let base = selected.identity().subject() == root;
            let known = if base {
                c.local_domain().known().to_vec()
            } else {
                vec![selected.identity().subject().clone()]
            };
            let mut conditional = Vec::new();
            if base {
                for member in c.local_domain().conditional() {
                    control
                        .checkpoint(Checkpoint::ObjectEvaluation)
                        .map_err(ConstructionFailure::from)?;
                    let ty = inputs
                        .archmap()
                        .snapshots
                        .iter()
                        .find(|s| s.id == member.subject().snapshot)
                        .and_then(|s| s.subjects.iter().find(|s| s.id == member.subject().subject))
                        .ok_or_else(|| {
                            ConstructionFailure::Inconsistent("条件付きsubjectがない".into())
                        })?
                        .ty
                        .clone();
                    conditional.push((ty, member.subject().clone(), member.owner_slot().clone()));
                }
            }
            let kind = match row.declaration().kind {
                "view" => "evaluate",
                "law" => "check",
                _ => {
                    return Err(ConstructionFailure::Inconsistent(
                        "対象読取りがLaw/viewでない".into(),
                    )
                    .into());
                }
            };
            let mut text = format!("readingResult={kind}({}", row.declaration().name);
            for binding in row.bindings() {
                control
                    .checkpoint(Checkpoint::ObjectEvaluation)
                    .map_err(ConstructionFailure::from)?;
                text.push_str(&format!(
                    ",bind.{}=@{}/{}",
                    binding.parameter().name,
                    binding.subject().snapshot,
                    binding.subject().subject
                ));
            }
            text.push(')');
            let mut prepared = prepare_shared_observed(inputs, &[&text], control).map_err(|f| {
                ObjectEvaluationFailure::Evaluation(Box::new(EvaluationFailure::Prepare(f)))
            })?;
            prepared.object = Some(ObjectContext {
                identity: selected.identity().clone(),
                instance: row.clone(),
                local_types,
                known,
                conditional,
            });
            ObjectEvaluationOutcome::Evaluated(Box::new(
                evaluate_observed(prepared, control)
                    .map_err(|f| ObjectEvaluationFailure::Evaluation(Box::new(f)))?,
            ))
        }
    };
    Ok(ObjectEvaluation {
        readings: readings.clone(),
        object,
        instance,
        outcome,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::construction::{construct, readings::object_reading_instances};
    fn quiet() -> Control {
        Control::new(control::Limits::default(), |_| control::Usage::default())
    }
    fn example(object: &str) -> ObservedEvaluation {
        let d = include_bytes!("../../tests/fixtures/object-instances.atoms.json");
        let l = include_str!("../../tests/fixtures/object-evaluation.law");
        let a = include_str!("../../tests/fixtures/object-instances.archmap.json");
        let defs = crate::definition::check_definitions(&[("definition0", d)]).unwrap();
        let digest = &defs.vocabularies["Instances"].digest;
        let inputs = Arc::new(
            input::check_inputs(
                input::InputSources::from_bytes(
                    vec![d.to_vec()],
                    l.replace("@INSTANCES_DIGEST@", digest).into_bytes(),
                    a.replace("@INSTANCES_DIGEST@", digest).into_bytes(),
                ),
                &mut quiet(),
            )
            .unwrap(),
        );
        let c = construct(&inputs, "Selected", "v", "A", &mut quiet()).unwrap();
        let plan = object_reading_instances(&inputs, &c, &mut quiet()).unwrap();
        let o = plan
            .objects()
            .iter()
            .position(|o| o.identity().subject().subject == object)
            .unwrap();
        let r = plan
            .instances()
            .iter()
            .position(|r| {
                r.declaration().name == "Selected.same" && r.bindings()[0].subject().subject == "p"
            })
            .unwrap();
        let result = evaluate_object_instance(inputs, &plan, o, r, &mut quiet()).unwrap();
        let ObjectEvaluationOutcome::Evaluated(result) = result.outcome else {
            panic!("評価対象")
        };
        *result
    }
    fn replay(result: &ObservedEvaluation, nodes: &[Node]) -> Result<(), ValidationFailure> {
        let mut control = quiet();
        let environment = environment::Environment::with_prepared(result.prepared(), &mut control)?;
        let mut graph = Graph::new(&control);
        graph.requests = result.prepared().requests().requests().to_vec();
        graph.checked_answers = result.answers.iter().cloned().enumerate().collect();
        graph.frames = result.frames.clone();
        graph.iterations = result.iterations.clone();
        graph.instances = result.instances.clone();
        graph.cases = result.cases.clone();
        graph.universal_witnesses = result.universal_witnesses.clone();
        for (index, node) in nodes.iter().enumerate() {
            graph.active = result.contexts[index];
            environment.validate(&graph, node)?;
            graph.push(node.clone())?;
        }
        for (request, answer) in graph.requests.iter().zip(&result.answers) {
            environment.validate_answer(&graph, request, answer)?;
        }
        Ok(())
    }
    #[test]
    fn object_domains_values_support_and_foreign_object_producers_are_independently_rechecked() {
        let mut result = example("p");
        replay(&result, &result.nodes).unwrap();
        let domain = result
            .nodes
            .iter()
            .position(|n| matches!(n.payload, Some(Payload::Domain { .. })))
            .unwrap();
        let value = result.answers[0].outputs["value"].0;
        for mutation in 0..6 {
            let mut nodes = result.nodes.clone();
            match mutation {
                0 => {
                    let Some(Payload::Domain { elements, .. }) = &mut nodes[domain].payload else {
                        unreachable!()
                    };
                    elements.clear();
                    nodes[domain].arguments.truncate(1);
                }
                1 => nodes[value].payload = Some(Payload::Scalar(Scalar::Bool(false))),
                2 => {
                    nodes[domain].support.clear();
                }
                3 => {
                    nodes[domain].scope.readings.insert("Foreign".into());
                }
                4 => {
                    let Some(Payload::Domain { elements, .. }) = &mut nodes[domain].payload else {
                        unreachable!()
                    };
                    let first = elements[0];
                    elements.push(first);
                    nodes[domain].arguments.push(first);
                }
                _ => {
                    let before = nodes[domain].support.len();
                    nodes[domain]
                        .support
                        .retain(|fact| fact.atom.as_deref() != Some("p-owner"));
                    assert!(nodes[domain].support.len() < before);
                }
            }
            assert!(
                matches!(replay(&result, &nodes), Err(ValidationFailure::Internal(_))),
                "mutation {mutation}"
            );
        }
        result.prepared.object = example("A").prepared.object;
        assert!(matches!(
            replay(&result, &result.nodes),
            Err(ValidationFailure::Internal(_))
        ));
    }
}
