//! Public projection of sealed root values. This never constructs a Graph or
//! evaluates the JSON that it emits.
use super::super::{
    evaluate::delivery::{ClosedAnswer, Counterexample, OwnedReason, OwnedValue},
    owned_scope::{DomainId, OwnedDomain, OwnedScope, ProducerId},
    result::{Decision, NodeRef, NodeType, ReasonKindOf, Scalar, ValidationFailure},
};
use archsig_common::{
    canonical::Json,
    control::{Checkpoint, Control},
};
use archsig_input::result::Signal;
use std::collections::BTreeMap;

/// The existing typed formatter omits references at the public boundary.
/// Native visibility diagnostics require their recorded coordinate owners and
/// are excluded before closed root evaluation starts.
pub(super) fn reason(reason: &OwnedReason) -> Json {
    assert!(
        !matches!(reason.kind, ReasonKindOf::VisibilityInsufficient { .. }),
        "closed root admission excludes native visibility diagnostics"
    );
    let mut result = reason.wire_with_references(|_| None);
    if let Json::Obj(fields) = &mut result {
        if let Some(Json::Obj(details)) = fields.get_mut("details") {
            details.remove("condition");
        }
    }
    result
}

#[derive(Default)]
pub(super) struct Projector {
    pub nodes: Vec<Json>,
    values: BTreeMap<ProducerId, NodeRef>,
    domains: BTreeMap<DomainId, NodeRef>,
    scalar_buckets: BTreeMap<u64, Vec<usize>>,
}
impl Projector {
    fn with_nodes(nodes: Vec<Json>) -> Self {
        let mut this = Self {
            nodes,
            ..Self::default()
        };
        for (index, node) in this.nodes.iter().enumerate() {
            if let Json::Obj(fields) = node {
                if let Some(value) = fields.get("value") {
                    this.scalar_buckets
                        .entry(super::super::result::canonical_fingerprint(value))
                        .or_default()
                        .push(index);
                }
            }
        }
        this
    }
    fn node(&mut self, ty: Json, value: Json) -> NodeRef {
        let reference = NodeRef(self.nodes.len());
        self.nodes.push(Json::obj([
            ("id", Json::str(format!("n{}", reference.0))),
            ("type", ty),
            ("state", Json::str("value")),
            ("conditions", Json::Arr(vec![])),
            ("reasons", Json::Arr(vec![])),
            ("value", value),
        ]));
        reference
    }
    fn scalar(
        &mut self,
        scalar: &Scalar,
        control: &Control,
        point: Checkpoint,
    ) -> Result<NodeRef, Signal> {
        control.checkpoint(point)?;
        let value = if super::super::path_value::contains_path(&scalar.ty(), &Control::unlimited())
            .expect("closed value type")
        {
            super::super::path_value::captured_wire(scalar, &Control::unlimited(), |child| {
                self.scalar(child, control, point)
                    .map_err(ValidationFailure::Stop)
            })
            .map_err(|failure| match failure {
                ValidationFailure::Stop(signal) => signal,
                _ => unreachable!("sealed value projection"),
            })?
        } else {
            scalar.wire()
        };
        // Public value sharing follows exact type and payload equality.
        let ty = NodeType::Value(scalar.ty()).wire();
        let fingerprint = super::super::result::canonical_fingerprint(&value);
        if let Some(index) = self.scalar_buckets.get(&fingerprint).and_then(|positions| positions.iter().copied().find(|&index| matches!(&self.nodes[index], Json::Obj(fields) if fields.get("type") == Some(&ty) && fields.get("value") == Some(&value) && matches!(fields.get("conditions"), Some(Json::Arr(v)) if v.is_empty()) && matches!(fields.get("reasons"), Some(Json::Arr(v)) if v.is_empty()) && fields.get("state") == Some(&Json::str("value"))))) {
            return Ok(NodeRef(index));
        }
        let reference = self.node(ty, value);
        self.scalar_buckets
            .entry(fingerprint)
            .or_default()
            .push(reference.0);
        Ok(reference)
    }

    fn value(
        &mut self,
        value: &OwnedValue,
        control: &Control,
        point: Checkpoint,
    ) -> Result<NodeRef, Signal> {
        if let Some(reference) = self.values.get(&value.producer) {
            return Ok(*reference);
        }
        let reference = self.scalar(&value.scalar, control, point)?;
        self.values.insert(value.producer.clone(), reference);
        Ok(reference)
    }
    fn domain(
        &mut self,
        domain: &OwnedDomain,
        ty: &archsig_common::types::Type,
        control: &Control,
        point: Checkpoint,
    ) -> Result<NodeRef, Signal> {
        if let Some(reference) = self.domains.get(&domain.identity()) {
            return Ok(*reference);
        }
        let mut members = vec![];
        for position in 0..domain.len().unwrap_or(0) {
            control.checkpoint(point)?;
            let member = domain.member(position).expect("finite owned domain member");
            let reference = self.scalar(member.value(), control, point)?;
            self.values.insert(member.producer(), reference);
            members.push(reference.wire());
        }
        let mut value = BTreeMap::from([
            (
                "kind".into(),
                Json::str(if domain.len().is_some() {
                    "finite"
                } else {
                    "type"
                }),
            ),
            ("type".into(), ty.wire()),
        ]);
        if domain.len().is_some() {
            value.insert("elements".into(), Json::Arr(members));
        }
        let value = Json::Obj(value.into());
        let fingerprint = super::super::result::canonical_fingerprint(&value);
        let reference = if let Some(index) = self.scalar_buckets.get(&fingerprint).and_then(|positions| positions.iter().copied().find(|&index| matches!(&self.nodes[index], Json::Obj(fields) if fields.get("type") == Some(&Json::str("Domain")) && fields.get("value") == Some(&value)))) { NodeRef(index) } else {
            let reference = self.node(Json::str("Domain"), value);
            self.scalar_buckets.entry(fingerprint).or_default().push(reference.0);
            reference
        };
        self.domains.insert(domain.identity(), reference);
        Ok(reference)
    }
    pub(super) fn scope(
        &mut self,
        scope: &OwnedScope,
        control: &Control,
        point: Checkpoint,
    ) -> Result<Json, Signal> {
        let mut quantifiers = vec![];
        for quantifier in &scope.quantifiers {
            control.checkpoint(point)?;
            let mut fields = BTreeMap::from([
                (
                    "kind".into(),
                    Json::str(
                        if quantifier.kind == archsig_input::law::ast::QuantKind::Forall {
                            "forall"
                        } else {
                            "exists"
                        },
                    ),
                ),
                ("name".into(), Json::str(&quantifier.name)),
                ("type".into(), quantifier.ty.wire()),
            ]);
            if let Some(domain) = &quantifier.domain {
                fields.insert(
                    "domain".into(),
                    self.domain(domain, &quantifier.ty, control, point)?.wire(),
                );
            }
            quantifiers.push(Json::Obj(fields.into()));
        }
        Ok(Json::obj([
            (
                "readings",
                Json::Arr(scope.readings.iter().map(Json::str).collect()),
            ),
            (
                "snapshots",
                Json::Arr(scope.snapshots.iter().map(Json::str).collect()),
            ),
            (
                "modes",
                Json::Arr(scope.modes.iter().map(Json::str).collect()),
            ),
            (
                "domain",
                Json::str(if scope.completions {
                    "all_completions"
                } else if scope.assignments {
                    "all_assignments"
                } else {
                    "finite_model"
                }),
            ),
            ("quantifiers", Json::Arr(quantifiers)),
            ("assumptions", Json::Arr(vec![])),
        ]))
    }
    fn counterexample(
        &mut self,
        example: &Counterexample,
        control: &Control,
        point: Checkpoint,
    ) -> Result<NodeRef, Signal> {
        let mut bindings = vec![];
        for binding in &example.bindings {
            bindings.push(Json::obj([
                ("name", Json::str(&binding.name)),
                ("value", self.value(&binding.value, control, point)?.wire()),
            ]));
        }
        let data = Json::obj([
            ("bindings", Json::Arr(bindings)),
            ("paths", Json::Arr(vec![])),
            ("left", self.value(&example.left, control, point)?.wire()),
            ("right", self.value(&example.right, control, point)?.wire()),
            (
                "facts",
                Json::Arr(example.facts.iter().map(|fact| fact.wire()).collect()),
            ),
        ]);
        Ok(self.node(
            Json::str("Counterexample"),
            Json::obj([("kind", Json::str("counterexample")), ("data", data)]),
        ))
    }
    pub(super) fn answer(
        &mut self,
        answer: &ClosedAnswer,
        kind: super::super::request::QuestionKind,
        control: &Control,
        point: Checkpoint,
    ) -> Result<Json, Signal> {
        let scope = self.scope(&answer.scope, control, point)?;
        let mut outputs = BTreeMap::new();
        if kind == super::super::request::QuestionKind::Evaluate
            && let Some(value) = &answer.value
        {
            outputs.insert("value".into(), self.value(value, control, point)?.wire());
        }
        let mut examples = vec![];
        if answer.status == Decision::Refuted {
            for example in &answer.counterexamples {
                examples.push(self.counterexample(example, control, point)?.wire());
            }
        }
        let mut ordered = answer.reasons.iter().collect::<Vec<_>>();
        ordered.sort_by_key(|reason| reason.sort_key());
        let mut reasons = ordered.into_iter().map(reason).collect();
        super::super::result::concise_reasons(&mut reasons);
        let mut fields = BTreeMap::from([
            ("id".into(), Json::str(&answer.id)),
            ("status".into(), Json::str(answer.status.wire())),
            ("outputs".into(), Json::Obj(outputs.into())),
            ("scope".into(), scope),
            ("reasons".into(), Json::Arr(reasons)),
            ("applicability".into(), Json::str(answer.applicability)),
        ]);
        if !examples.is_empty() {
            fields.insert("counterexamples".into(), Json::Arr(examples));
        }
        Ok(Json::Obj(fields.into()))
    }
}

pub(super) fn run(
    run: &super::super::evaluate::delivery::ClosedRun,
    control: &Control,
    point: Checkpoint,
) -> Result<Json, Signal> {
    use super::super::evaluate::delivery::{DeliveryAnswer, DeliveryReason};
    let recorded = run
        .answers
        .iter()
        .filter_map(|answer| match answer {
            DeliveryAnswer::Recorded(answer) => Some(answer.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let nodes = run
        .tail
        .as_ref()
        .map(|tail| &tail.graph.nodes[..])
        .unwrap_or(&[]);
    let mut result = super::super::result::project_recorded_tail(
        &run.prepared,
        nodes,
        &recorded,
        &[],
        run.status,
        control,
        point,
    )?;
    let Json::Obj(document) = &mut result else {
        unreachable!("public recorded projection")
    };
    let mut rows_wire = document.remove("answers").expect("recorded answers");
    let Json::Arr(recorded_rows) = &mut rows_wire else {
        unreachable!("recorded answers")
    };
    let recorded_rows = std::mem::take(recorded_rows);
    let mut nodes_wire = document.remove("nodes").expect("recorded nodes");
    let Json::Arr(recorded_nodes) = &mut nodes_wire else {
        unreachable!("recorded nodes")
    };
    let recorded_nodes = std::mem::take(recorded_nodes);
    let Some(Json::Arr(_)) = document.remove("issues") else {
        unreachable!("recorded issues")
    };
    let mut projector = Projector::with_nodes(recorded_nodes);
    let mut recorded_rows = recorded_rows.into_iter();
    let mut rows = vec![];
    for (index, answer) in run.answers.iter().enumerate() {
        control.checkpoint(point)?;
        let row = match answer {
            DeliveryAnswer::Closed(answer) => projector.answer(
                answer,
                run.prepared.requests().requests()[index].kind,
                control,
                point,
            )?,
            DeliveryAnswer::Recorded(answer) => {
                let mut row = recorded_rows.next().expect("recorded answer order");
                if let Some(tail) = &run.tail {
                    if run.prepared.requests().requests()[tail.request_index].id == answer.id {
                        let Json::Obj(fields) = &mut row else {
                            unreachable!("answer object")
                        };
                        if tail.retained.scope != OwnedScope::default() {
                            // Pure identity conversion uses correspondences captured before
                            // Stop. Generic Scope::merge keeps occurrence/activation identity
                            // until the final display boundary.
                            let mut scope = tail
                                .retained
                                .references
                                .map_scope(&answer.scope)
                                .expect("retained root owns every tail scope correspondence");
                            scope.merge(&tail.retained.scope);
                            fields.insert("scope".into(), projector.scope(&scope, control, point)?);
                        }
                        let Some(Json::Arr(reasons)) = fields.get_mut("reasons") else {
                            unreachable!("answer reasons")
                        };
                        let mut ordered = tail
                            .retained
                            .reasons
                            .iter()
                            .map(|reason| (reason.sort_key(), self::reason(reason)))
                            .chain(answer.reasons.iter().map(|reason| {
                                (
                                    reason.sort_key(),
                                    super::super::result::public_reason_wire(reason),
                                )
                            }))
                            .collect::<Vec<_>>();
                        ordered.sort_by(|left, right| left.0.cmp(&right.0));
                        *reasons = ordered.into_iter().map(|(_, reason)| reason).collect();
                        super::super::result::concise_reasons(reasons);
                        if tail.retained.root_complete
                            && run.prepared.requests().requests()[tail.request_index].kind
                                == super::super::request::QuestionKind::Evaluate
                        {
                            if let Some(value) = &tail.retained.value {
                                let Some(Json::Obj(outputs)) = fields.get_mut("outputs") else {
                                    unreachable!("answer outputs")
                                };
                                outputs.insert(
                                    "value".into(),
                                    projector.value(value, control, point)?.wire(),
                                );
                            }
                        }
                    }
                }
                row
            }
        };
        rows.push(row);
    }
    let issues = super::ordered_issues(run)
        .into_iter()
        .map(|issue| match issue {
            DeliveryReason::Closed(issue) => reason(issue),
            DeliveryReason::Recorded(issue) => super::super::result::public_reason_wire(issue),
        })
        .collect();
    document.insert("answers".into(), Json::Arr(rows));
    document.insert("issues".into(), Json::Arr(issues));
    document.insert("nodes".into(), Json::Arr(projector.nodes));
    run.prepared
        .inputs()
        .sources()
        .add_location_positions(&mut result);
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::super::super::owned_scope::{Identities, OwnedQuantifier};
    use super::*;
    use archsig_common::types::Type;
    use std::sync::Arc;
    #[test]
    fn projection_shares_equal_domain_records_without_collapsing_real_activations() {
        let mut identities = Identities::default();
        let mut scope = OwnedScope::default();
        for _ in 0..2 {
            let domain = identities
                .shared_domain(vec![Arc::new(Scalar::Z(1.into()))])
                .unwrap();
            scope.quantifiers.push(OwnedQuantifier {
                kind: archsig_input::law::ast::QuantKind::Forall,
                name: "x".into(),
                ty: Type::Z,
                domain: Some(domain),
                occurrence: (1, 2),
                context: Some(identities.activation().unwrap()),
                assembly_instance: None,
            });
        }
        let mut projector = Projector::default();
        let Json::Obj(ref wire) = projector
            .scope(&scope, &Control::unlimited(), Checkpoint::Expression)
            .unwrap()
        else {
            panic!("scope")
        };
        let Json::Arr(quantifiers) = &wire["quantifiers"] else {
            panic!("quantifiers")
        };
        assert_eq!(
            quantifiers.len(),
            2,
            "equal public descriptors retain actual multiplicity"
        );
        assert_eq!(
            projector.nodes.len(),
            2,
            "one scalar and one equal public Domain record"
        );
        let numeric = projector
            .scalar(
                &Scalar::Z(1.into()),
                &Control::unlimited(),
                Checkpoint::Expression,
            )
            .unwrap();
        let text = projector
            .scalar(
                &Scalar::Text("1".into()),
                &Control::unlimited(),
                Checkpoint::Expression,
            )
            .unwrap();
        assert_ne!(
            numeric, text,
            "same wire payload with different native type stays distinct"
        );
    }
}
