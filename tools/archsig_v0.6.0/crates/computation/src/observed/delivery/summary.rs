//! Terminal summary from owned results. No Graph lookup or evaluation occurs.
use super::super::{
    evaluate::delivery::{ClosedAnswer, Counterexample, OwnedReason},
    request::QuestionKind,
    result::{Decision, Fact, ReasonKindOf},
    summary as formatting,
};
use archsig_common::{canonical::Json, internal::InternalError};
use std::collections::BTreeMap;

/// The display borrows an unfinished recorded tail instead of fabricating a raw
/// ObservedEvaluation for earlier sealed answers.
pub(super) fn run_summary(
    run: &super::super::evaluate::delivery::ClosedRun,
    status: &str,
    code: u8,
    issues: &[Json],
) -> Json {
    use super::super::evaluate::delivery::DeliveryAnswer;
    let answers = run
        .answers
        .iter()
        .map(|answer| match answer {
            DeliveryAnswer::Closed(answer) => {
                let request = run
                    .prepared
                    .requests()
                    .requests()
                    .iter()
                    .find(|request| request.id == answer.id)
                    .expect("closed answer request");
                closed_answer_summary(answer, request.kind, super::project::reason)
                    .expect("sealed scalar summary needs no Graph")
            }
            DeliveryAnswer::Recorded(answer) => {
                let Some(tail) = run.tail.as_ref().filter(|tail| {
                    run.prepared.requests().requests()[tail.request_index].id == answer.id
                }) else {
                    return formatting::recorded_answer_summary(&run.prepared, &[], answer);
                };
                let request = &run.prepared.requests().requests()[tail.request_index];
                let mut row =
                    formatting::recorded_answer_summary(&run.prepared, &tail.graph.nodes, answer);
                let Json::Obj(fields) = &mut row else {
                    unreachable!("answer summary object")
                };
                let mut reasons = tail
                    .retained
                    .reasons
                    .iter()
                    .filter(|reason| {
                        answer.status == Decision::Undetermined
                            || !matches!(reason.kind, ReasonKindOf::Missing)
                    })
                    .map(|reason| {
                        (
                            reason.sort_key(),
                            formatting::notice(&super::project::reason(reason)),
                        )
                    })
                    .chain(
                        answer
                            .reasons
                            .iter()
                            .filter(|reason| {
                                answer.status == Decision::Undetermined
                                    || !matches!(reason.kind, ReasonKindOf::Missing)
                            })
                            .map(|reason| (reason.sort_key(), formatting::notice(&reason.wire()))),
                    )
                    .collect::<Vec<_>>();
                reasons.sort_by(|left, right| left.0.cmp(&right.0));
                let mut reasons = reasons
                    .into_iter()
                    .map(|(_, reason)| reason)
                    .collect::<Vec<_>>();
                super::super::result::concise_reasons(&mut reasons);
                if reasons.is_empty() {
                    fields.remove("reasons");
                } else {
                    fields.insert("reasons".into(), Json::Arr(reasons));
                }
                if tail.retained.root_complete {
                    if !fields.contains_key("applicability") {
                        fields.insert("applicability".into(), Json::str("applicable"));
                    }
                    if request.kind == QuestionKind::Evaluate
                        && let Some(value) = &tail.retained.value
                    {
                        let Some(Json::Obj(outputs)) = fields.get_mut("outputs") else {
                            unreachable!("summary outputs")
                        };
                        outputs.insert(
                            "value".into(),
                            formatting::scalar_node_summary(&value.scalar)
                                .expect("retained root scalar summary needs no Graph"),
                        );
                    }
                }
                row
            }
        })
        .collect();
    formatting::summary_document(answers, status, code, issues)
}

pub(in crate::observed) fn closed_answer_summary(
    answer: &ClosedAnswer,
    question: QuestionKind,
    mut reason_wire: impl FnMut(&OwnedReason) -> Json,
) -> Result<Json, InternalError> {
    let mut outputs = BTreeMap::new();
    if question == QuestionKind::Evaluate
        && let Some(value) = &answer.value
    {
        outputs.insert(
            "value".into(),
            formatting::scalar_node_summary(&value.scalar)?,
        );
    }
    let mut row = BTreeMap::from([
        ("id".into(), Json::str(&answer.id)),
        ("question".into(), Json::str(question.wire())),
        ("status".into(), Json::str(answer.status.wire())),
        ("outputs".into(), Json::Obj(outputs.into())),
        ("applicability".into(), Json::str(answer.applicability)),
    ]);
    let mut reasons = answer
        .reasons
        .iter()
        .filter(|reason| {
            answer.status == Decision::Undetermined || !matches!(reason.kind, ReasonKindOf::Missing)
        })
        .map(|reason| formatting::notice(&reason_wire(reason)))
        .collect::<Vec<_>>();
    super::super::result::concise_reasons(&mut reasons);
    if !reasons.is_empty() {
        row.insert("reasons".into(), Json::Arr(reasons));
    }
    if answer.status == Decision::Refuted && !answer.counterexamples.is_empty() {
        row.insert(
            "counterexamples_total".into(),
            Json::Nat(answer.counterexamples.len() as u64),
        );
        row.insert(
            "counterexamples".into(),
            Json::Arr(
                answer
                    .counterexamples
                    .iter()
                    .take(formatting::EXAMPLE_LIMIT)
                    .map(counterexample_summary)
                    .collect::<Result<_, _>>()?,
            ),
        );
    }
    Ok(Json::Obj(row.into()))
}

fn counterexample_summary(example: &Counterexample) -> Result<Json, InternalError> {
    let value = |value: &super::super::evaluate::delivery::OwnedValue| {
        formatting::scalar_node_summary(&value.scalar).map(formatting::bounded_counterexample_value)
    };
    let bindings = example
        .bindings
        .iter()
        .take(formatting::ITEM_LIMIT)
        .map(|binding| Ok((binding.name.as_str(), value(&binding.value)?)))
        .collect::<Result<Vec<_>, InternalError>>()?;
    Ok(formatting::comparison_summary(
        value(&example.left)?,
        value(&example.right)?,
        example.bindings.len(),
        bindings.into_iter(),
        example.facts.iter().map(Fact::wire),
        example.operator,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::observed::{
        evaluate::delivery::{OwnedBinding, OwnedValue},
        evaluate_observed,
        owned_scope::Identities,
        prepare_observed,
        result::{NodeRef, ObservedEvaluation, Payload, Scalar},
    };
    use archsig_common::{control::Control, types::Type};
    use std::sync::Arc;

    fn value(
        raw: &ObservedEvaluation,
        mut reference: NodeRef,
        identities: &mut Identities,
        values: &mut BTreeMap<NodeRef, OwnedValue>,
    ) -> OwnedValue {
        while let Some(Payload::Evaluation {
            value: Some(next), ..
        }) = &raw.nodes[reference.0].payload
        {
            reference = *next;
        }
        if let Some(value) = values.get(&reference) {
            return value.clone();
        }
        let Some(Payload::Scalar(scalar)) = &raw.nodes[reference.0].payload else {
            panic!("fixture scalar")
        };
        let value = OwnedValue {
            producer: identities.producer().unwrap(),
            scalar: scalar.clone(),
        };
        values.insert(reference, value.clone());
        value
    }
    #[test]
    fn delivery_owned_counterexample_summary_matches_the_recorded_typed_values() {
        let control = Control::unlimited();
        let sources = archsig_input::input::InputSources::from_bytes(
            vec![include_bytes!("../../../../../tests/fixtures/counter.atoms.json").to_vec()],
            include_bytes!("../../../../../tests/fixtures/counter.law").to_vec(),
            include_str!("../../../../../tests/fixtures/counter.archmap.json")
                .replace("\"value\": \"2\"", "\"value\": \"-1\"")
                .into_bytes(),
        );
        let prepared = prepare_observed(
            sources,
            &["q=check(CountCheck.nonnegative,s=@v/s)"],
            &control,
        )
        .unwrap();
        let raw = evaluate_observed(prepared, &control).unwrap();
        let answer = &raw.answers[0];
        assert_eq!(answer.status, Decision::Refuted);
        let mut identities = Identities::default();
        let mut values = BTreeMap::new();
        let examples = answer
            .evidence
            .iter()
            .filter_map(|reference| {
                let Some(Payload::Counterexample {
                    bindings,
                    left,
                    right,
                    facts,
                }) = &raw.nodes[reference.0].payload
                else {
                    return None;
                };
                let bindings = bindings
                    .iter()
                    .map(|binding| OwnedBinding {
                        name: binding.name.clone(),
                        value: value(&raw, binding.value, &mut identities, &mut values),
                    })
                    .collect();
                Some(Counterexample {
                    bindings,
                    left: value(&raw, *left, &mut identities, &mut values),
                    right: value(&raw, *right, &mut identities, &mut values),
                    facts: facts.clone(),
                    operator: Some(archsig_input::law::ast::BinOp::Ge),
                })
            })
            .collect::<Vec<_>>();
        assert_eq!(examples.len(), 1);
        let closed = ClosedAnswer {
            id: answer.id.clone(),
            status: answer.status,
            value: Some(OwnedValue {
                producer: identities.producer().unwrap(),
                scalar: Arc::new(Scalar::Bool(false)),
            }),
            applicability: "applicable",
            scope: Default::default(),
            reasons: vec![],
            counterexamples: examples,
        };
        let expected = formatting::recorded_answer_summary(raw.prepared(), &raw.nodes, answer);
        assert_eq!(
            closed_answer_summary(&closed, QuestionKind::Check, |_| panic!(
                "no fixture reasons"
            ))
            .unwrap(),
            expected
        );
    }
    #[test]
    fn delivery_owned_scalar_summary_keeps_utf8_bytes_and_empty_path_values() {
        let short = Scalar::Text("界".repeat(84));
        assert_eq!(
            formatting::scalar_node_summary(&short).unwrap(),
            Json::obj([
                ("type", Type::Text.wire()),
                ("value", Json::str("界".repeat(84)))
            ])
        );
        let long = Scalar::Text("界".repeat(85));
        assert_eq!(
            formatting::scalar_node_summary(&long).unwrap(),
            Json::obj([("type", Type::Text.wire()), ("value_bytes", Json::Nat(257))])
        );
        let path = Scalar::Path(Box::new(crate::observed::path_value::PathValue {
            reading: "R".into(),
            snapshot: "v".into(),
            subject: "s".into(),
            entity: "Counter.State".into(),
            step: None,
        }));
        assert_eq!(
            formatting::scalar_node_summary(&path).unwrap(),
            Json::obj([("type", path.ty().wire())])
        );
        let empty = Scalar::List {
            element: path.ty(),
            items: vec![],
        };
        assert_eq!(
            formatting::scalar_node_summary(&empty).unwrap(),
            Json::obj([("type", empty.ty().wire()), ("value", Json::Arr(vec![]))])
        );
        let none = Scalar::Option {
            element: path.ty(),
            value: None,
        };
        assert_eq!(
            formatting::scalar_node_summary(&none).unwrap(),
            Json::obj([
                ("type", none.ty().wire()),
                ("value", Json::obj([("none", Json::Bool(true))]))
            ])
        );
    }
}
