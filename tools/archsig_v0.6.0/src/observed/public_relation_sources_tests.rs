use super::*;
use crate::law::model::Signature;
use crate::observed::construction_result::Witness;
use crate::observed::{call::Context, input::InputSources, public_compare::relation_sources};
#[allow(dead_code, unused_imports)]
mod relation_fixture {
    use crate as archsig;
    include!("../../tests/common/public_relation.rs");
}
fn inputs(extra: &str) -> InputSources {
    relation_fixture::input(extra, false)
}
fn inputs_mode(extra: &str, missing: bool) -> InputSources {
    relation_fixture::input(extra, missing)
}
fn setup(extra: &str) -> (PreparedObserved, Graph, NodeRef, NodeRef) {
    let sources = inputs(extra);
    let old =
        evaluate_observed_bytes(sources.clone(), &[E, ALIAS], &mut Control::unlimited()).unwrap();
    assert_eq!(old.status(), "complete", "{:?}", old.issues);
    let mut graph = rebuild_for_origin_and_support_recheck(&old, &old.nodes).unwrap();
    let prepared = crate::observed::prepare_observed(
        sources,
        &[
            E,
            ALIAS,
            "rel=compare($e.value,to=$alias.value,kind=relation)",
        ],
        &mut Control::unlimited(),
    )
    .unwrap();
    graph.requests = prepared.requests().requests().to_vec();
    graph.active = Context {
        request: 2,
        ..Context::default()
    };
    (
        prepared,
        graph,
        old.answers[0].outputs["value"],
        old.answers[1].outputs["value"],
    )
}
fn check_graph(prepared: &PreparedObserved, graph: &Graph) {
    let mut control = Control::unlimited();
    let env = Environment::with_prepared(prepared, &mut control).unwrap();
    let mut rebuilt = Graph::new(&control);
    rebuilt.requests = graph.requests.clone();
    rebuilt.checked_answers = graph.checked_answers.clone();
    rebuilt.frames = graph.frames.clone();
    rebuilt.instances = graph.instances.clone();
    rebuilt.iterations = graph.iterations.clone();
    rebuilt.cases = graph.cases.clone();
    rebuilt.universal_witnesses = graph.universal_witnesses.clone();
    for (index, node) in graph.nodes.iter().enumerate() {
        rebuilt.active = graph.context_at(index);
        env.validate(&rebuilt, node)
            .unwrap_or_else(|e| panic!("node {index}: {e:?}"));
        rebuilt.push(node.clone()).unwrap();
    }
}
#[test]
fn original_relation_bindings_feed_the_existing_ast_evaluator_and_recheck() {
    let (prepared, mut graph, left, right) = setup(
        "relation aliasing(e:Hop,f:Hop) when source(path(e))=source(path(f)) and target(path(e))=target(path(f)):path(e)=path(f);",
    );
    let mut control = Control::unlimited();
    let env = Environment::with_prepared(&prepared, &mut control).unwrap();
    let request = &prepared.requests().requests()[2];
    let (w, domains) = relation_sources::prepare_sources(
        &prepared,
        &env,
        &mut graph,
        request,
        left,
        right,
        &mut control,
    )
    .unwrap();
    let table = &w.relation_family.as_ref().unwrap().table;
    assert_eq!(table.declarations.len(), 1);
    let (row, original) = table
        .instances
        .iter()
        .enumerate()
        .find(|(_, row)| {
            row.bindings
                .iter()
                .map(|(_, value)| value)
                .all(|v| matches!(v, Scalar::Subject { subject, .. } if subject=="e"))
        })
        .unwrap();
    assert_eq!(original.guard, Some(true));
    let instance = domains.instances[row].unwrap();
    let declaration = &table.declarations[0];
    let Signature::Relation {
        guard, left, right, ..
    } = &declaration.signature
    else {
        panic!()
    };
    for expression in [guard.unwrap(), *left, *right] {
        let value = super::super::relation_side(
            &env,
            &mut graph,
            &mut control,
            request,
            declaration,
            instance,
            expression,
        )
        .unwrap();
        assert!(value.value.is_some());
        assert!(value.reasons.is_empty());
    }
    assert_eq!(
        graph.active,
        Context {
            request: 2,
            ..Context::default()
        }
    );
    check_graph(&prepared, &graph);
}
#[test]
fn a_nonfinite_parameter_domain_is_not_published_as_empty_finite_exhaustion() {
    let (prepared, mut graph, left, right) =
        setup("relation unbounded(n:Z,e:Hop):path(e)=path(e);");
    let mut control = Control::unlimited();
    let env = Environment::with_prepared(&prepared, &mut control).unwrap();
    let (w, domains) = relation_sources::prepare_sources(
        &prepared,
        &env,
        &mut graph,
        &prepared.requests().requests()[2],
        left,
        right,
        &mut control,
    )
    .unwrap();
    assert_eq!(
        w.relation_family
            .as_ref()
            .unwrap()
            .table
            .outside_finite
            .len(),
        1
    );
    assert_eq!(domains.sources.len(), 1);
    assert_eq!(domains.domains, vec![None]);
    assert!(domains.instances.is_empty());
    check_graph(&prepared, &graph);
}
#[test]
fn helper_and_let_occurrences_keep_their_original_relation_bindings() {
    let (prepared, mut graph, left, right) = setup(
        "relation wrapped_relation(e:Hop,flag:Bool) when flag or not flag:lexical(e)=(let p=step(e) in p);",
    );
    let mut control = Control::unlimited();
    let env = Environment::with_prepared(&prepared, &mut control).unwrap();
    let request = &prepared.requests().requests()[2];
    let (w, domains) = relation_sources::prepare_sources(
        &prepared,
        &env,
        &mut graph,
        request,
        left,
        right,
        &mut control,
    )
    .unwrap();
    let table = &w.relation_family.as_ref().unwrap().table;
    let row = table
        .instances
        .iter()
        .position(
            |row| matches!(&row.bindings[0].1, Scalar::Subject { subject, .. } if subject=="e"),
        )
        .unwrap();
    let declaration = &table.declarations[0];
    let Signature::Relation {
        guard, left, right, ..
    } = declaration.signature
    else {
        panic!()
    };
    for expression in [guard.unwrap(), left, right] {
        let value = super::super::relation_side(
            &env,
            &mut graph,
            &mut control,
            request,
            declaration,
            domains.instances[row].unwrap(),
            expression,
        )
        .unwrap();
        assert!(value.value.is_some());
        assert!(value.reasons.is_empty());
    }
    assert!(!graph.frames.is_empty());
    check_graph(&prepared, &graph);
}
#[test]
fn an_inactive_guard_cannot_publish_a_body_value() {
    let (prepared, mut graph, left, right) =
        setup("relation inactive(e:Hop) when false:path(e)=path(e);");
    let mut control = Control::unlimited();
    let env = Environment::with_prepared(&prepared, &mut control).unwrap();
    let request = &prepared.requests().requests()[2];
    let (w, domains) = relation_sources::prepare_sources(
        &prepared,
        &env,
        &mut graph,
        request,
        left,
        right,
        &mut control,
    )
    .unwrap();
    let table = &w.relation_family.as_ref().unwrap().table;
    let declaration = &table.declarations[0];
    let Signature::Relation { guard, left, .. } = declaration.signature else {
        panic!()
    };
    let instance = domains.instances[0].unwrap();
    let value = super::super::relation_side(
        &env,
        &mut graph,
        &mut control,
        request,
        declaration,
        instance,
        guard.unwrap(),
    )
    .unwrap();
    assert_eq!(
        graph.scalar(value.value.unwrap()).unwrap(),
        &Scalar::Bool(false)
    );
    let count = graph.nodes.len();
    assert!(
        super::super::relation_side(
            &env,
            &mut graph,
            &mut control,
            request,
            declaration,
            instance,
            left
        )
        .is_err()
    );
    assert_eq!(graph.nodes.len(), count);
    check_graph(&prepared, &graph);
}
const ALIAS_RELATION: &str = "relation aliasing(e:Hop,f:Hop) when source(path(e))=source(path(f)) and target(path(e))=target(path(f)):path(e)=path(f);";
fn public(extra: &str, queries: &[&str]) -> ObservedEvaluation {
    let result =
        evaluate_observed_bytes(inputs(extra), queries, &mut Control::unlimited()).unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    result
}
#[test]
fn public_relation_uses_original_rules_and_retains_a_closed_word_certificate() {
    let queries = [
        E,
        ALIAS,
        "compared=compare($e.value,to=$alias.value,kind=relation)",
    ];
    let without = public("", &queries);
    assert_eq!(without.answers[2].status, Decision::Refuted);
    let with = public(ALIAS_RELATION, &queries);
    assert_eq!(with.answers[2].status, Decision::Established);
    assert!(with.answers[2].outputs.contains_key("comparison"));
    assert!(
        with.answers[2]
            .scope
            .quantifiers
            .iter()
            .any(|q| q.name == "relation_word" && q.domain.is_some())
    );
    let claim = with.answers[2].claim.unwrap();
    let Payload::Construction(value) = with.nodes[claim.0].payload.as_ref().unwrap() else {
        panic!()
    };
    let Witness::Compare(w) = &value.witness else {
        panic!()
    };
    let D::Comparison(part) = &value.data else {
        panic!()
    };
    assert!(part.wire(w).canonical().contains("relation_equal"));
    let proof = with.answers[2].evidence[1];
    let Payload::Construction(proof) = with.nodes[proof.0].payload.as_ref().unwrap() else {
        panic!()
    };
    let D::Comparison(Part::RelationDerived { data, .. }) = &proof.data else {
        panic!()
    };
    assert!(
        matches!(data.as_ref(), crate::observed::public_compare::relations::Data::Normalization{steps,..} if !steps.is_empty())
    );
}
#[test]
fn composed_query_words_are_compared_in_their_actual_rewrite_context() {
    let with = public(
        ALIAS_RELATION,
        &[
            E,
            ALIAS,
            fixture::F,
            fixture::C,
            "other=compose($alias.value,then=$f.value)",
            "compared=compare($c.operation,to=$other.operation,kind=relation)",
        ],
    );
    assert_eq!(with.answers[5].status, Decision::Established);
    let without = public(
        "",
        &[
            E,
            ALIAS,
            fixture::F,
            fixture::C,
            "other=compose($alias.value,then=$f.value)",
            "compared=compare($c.operation,to=$other.operation,kind=relation)",
        ],
    );
    assert_eq!(without.answers[5].status, Decision::Refuted);
}

#[test]
fn an_unknown_guard_stays_undetermined_and_needed_keeps_its_original_slot() {
    let sources = inputs_mode(relation_fixture::PENDING_RELATION, true);
    let result = evaluate_observed_bytes(
        sources,
        &[
            E,
            ALIAS,
            "compared=compare($e.value,to=$alias.value,kind=relation)",
            "observe=needed($compared)",
        ],
        &mut Control::unlimited(),
    )
    .unwrap();
    assert!(
        result
            .issues
            .iter()
            .all(|reason| matches!(reason.kind, ReasonKind::Missing)),
        "{:?}",
        result.issues
    );
    assert_eq!(result.answers[0].status, Decision::Established);
    assert_eq!(result.answers[2].status, Decision::Undetermined);
    assert!(result.answers[2].reasons.iter().any(|reason| {
        matches!(reason.kind, ReasonKind::Missing)
            && reason
                .missing
                .iter()
                .any(|fact| fact.field.as_deref() == Some("Paths.Guard.flag"))
    }));
    assert!(result.answers[3].outputs.contains_key("plan"));
    let Payload::ObservationPlan { requirements, .. } = result.nodes
        [result.answers[3].outputs["plan"].0]
        .payload
        .as_ref()
        .unwrap()
    else {
        panic!()
    };
    assert_eq!(requirements.len(), 1);
    let crate::canonical::Json::Obj(ref fields) = requirements[0].wire() else {
        panic!()
    };
    assert_eq!(
        fields["field"],
        crate::canonical::Json::obj([
            ("snapshot", crate::canonical::Json::str("v")),
            ("subject", crate::canonical::Json::str("guard")),
            ("field", crate::canonical::Json::str("Paths.Guard.flag"))
        ])
    );

    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
}

#[test]
fn an_invalid_relation_refutes_constructibility_instead_of_congruence_membership() {
    let result = evaluate_observed_bytes(
        inputs("relation invalid(e:Hop):path(e)=identity(source(path(e)));"),
        &[
            E,
            ALIAS,
            "compared=compare($e.value,to=$alias.value,kind=relation)",
        ],
        &mut Control::unlimited(),
    )
    .unwrap();
    let answer = &result.answers[2];
    assert_eq!(answer.status, Decision::Refuted, "{:?}", result.issues);
    assert!(!answer.outputs.contains_key("comparison"));
    assert!(answer.reasons.iter().any(|r| matches!(
        r.kind,
        ReasonKind::ConditionFailed {
            construction: "comparison",
            ..
        }
    )));
    assert!(
        result
            .issues
            .iter()
            .all(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. })),
        "{:?}",
        result.issues
    );
    let Payload::Construction(claim) = result.nodes[answer.claim.unwrap().0]
        .payload
        .as_ref()
        .unwrap()
    else {
        panic!()
    };
    let Witness::Compare(w) = &claim.witness else {
        panic!()
    };
    let D::Comparison(part) = &claim.data else {
        panic!()
    };
    assert!(part.wire(w).canonical().contains("constructible"));
    assert!(!answer.evidence.is_empty());
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
}
#[test]
fn a_noncomposable_relation_body_retains_the_original_path_failure() {
    let script = "relation invalid(e:Hop):then(path(e),path(e))=then(path(e),path(e));";
    let result = evaluate_observed_bytes(
        inputs(script),
        &[
            E,
            ALIAS,
            "compared=compare($e.value,to=$alias.value,kind=relation)",
        ],
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(
        result.answers[2].status,
        Decision::Refuted,
        "{:?}",
        result.issues
    );
    assert!(!result.answers[2].outputs.contains_key("comparison"));
    assert!(
        result.answers[2]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
    );
    assert!(
        result
            .issues
            .iter()
            .all(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. })),
        "{:?}",
        result.issues
    );
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    let inactive = public(
        "relation inactive(e:Hop) when false:then(path(e),path(e))=then(path(e),path(e));",
        &[
            E,
            ALIAS,
            "compared=compare($e.value,to=$alias.value,kind=relation)",
        ],
    );
    assert_eq!(inactive.answers[2].status, Decision::Refuted);
    assert!(inactive.answers[2].outputs.contains_key("comparison"));
    assert!(inactive.answers[2].reasons.is_empty());
}

fn known_failure_with_an_independent_nonfinite_relation(invalid: &str, expected: &str) {
    let script = format!("{invalid} relation unbounded(n:Z,e:Hop):path(e)=path(e);");
    let result = evaluate_observed_bytes(
        inputs(&script),
        &[
            E,
            ALIAS,
            "compared=compare($e.value,to=$alias.value,kind=relation)",
        ],
        &mut Control::unlimited(),
    )
    .unwrap();
    let answer = &result.answers[2];
    assert_eq!(answer.status, Decision::Refuted, "{:?}", result.issues);
    assert!(!answer.outputs.contains_key("comparison"));
    assert!(!answer.evidence.is_empty());
    assert!(
        answer.reasons.iter().any(|reason| matches!(
            reason.kind,
            ReasonKind::ConditionFailed { construction, .. } if construction == expected
        )),
        "{:?}",
        answer.reasons
    );
    assert!(
        result
            .issues
            .iter()
            .all(|reason| matches!(reason.kind, ReasonKind::ConditionFailed { .. })),
        "{:?}",
        result.issues
    );
    let claim = answer.claim.unwrap();
    let Payload::Construction(value) = result.nodes[claim.0].payload.as_ref().unwrap() else {
        panic!()
    };
    let Witness::Compare(witness) = &value.witness else {
        panic!()
    };
    let D::Comparison(part) = &value.data else {
        panic!()
    };
    assert!(part.wire(witness).canonical().contains("constructible"));
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
}

#[test]
fn an_independent_nonfinite_domain_does_not_hide_a_known_relation_refutation() {
    known_failure_with_an_independent_nonfinite_relation(
        "relation invalid(e:Hop):path(e)=identity(source(path(e)));",
        "comparison",
    );
}

#[test]
fn an_independent_nonfinite_domain_does_not_hide_a_known_path_construction_failure() {
    known_failure_with_an_independent_nonfinite_relation(
        "relation invalid(e:Hop):then(path(e),path(e))=then(path(e),path(e));",
        "evaluation",
    );
}

fn partial_domain_keeps_known_failure(outside: bool, body: &str, construction: &str) {
    let snapshot = if outside { "v" } else { "w" };
    let one = format!("one=evaluate(Reservations.route,e=@{snapshot}/e)");
    let two = format!("two=evaluate(Reservations.route,e=@{snapshot}/k)");
    let result = evaluate_observed_bytes(
        relation_fixture::partial_domain_input(outside, body),
        &[
            &one,
            &two,
            "compared=compare($one.value,to=$two.value,kind=relation)",
        ],
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(result.answers[0].status, Decision::Established);
    assert_eq!(result.answers[1].status, Decision::Established);
    let answer = &result.answers[2];
    assert_eq!(answer.status, Decision::Refuted, "{:?}", result.issues);
    assert!(!answer.outputs.contains_key("comparison"));
    assert!(!answer.evidence.is_empty());
    assert!(answer.reasons.iter().any(|reason| matches!(reason.kind,
        ReasonKind::ConditionFailed { construction: actual, .. } if actual == construction)));
    assert!(
        result.issues.iter().all(|reason| matches!(
            reason.kind,
            ReasonKind::ConditionFailed { .. } | ReasonKind::Missing
        )),
        "{:?}",
        result.issues
    );
    if !outside {
        assert!(
            answer.reasons.iter().any(|reason| reason
                .missing
                .iter()
                .any(|fact| fact.snapshot == "v"
                    && fact.subject == "e"
                    && fact.field.as_deref() == Some("Reservations.Reserve.owner")))
        );
    }
    let (index, _) = result.nodes.iter().enumerate().find(|(_, node)| matches!(
        &node.payload, Some(Payload::Construction(value)) if matches!(
            &value.data, D::Comparison(Part::RelationSource(data)) if matches!(
                &data.kind, relation_sources::Kind::Domain { finite: false, members, .. } if !members.is_empty())))).unwrap();
    let Payload::Construction(value) = result.nodes[index].payload.as_ref().unwrap() else {
        panic!()
    };
    let Witness::Compare(witness) = &value.witness else {
        panic!()
    };
    let D::Comparison(part) = &value.data else {
        panic!()
    };
    assert!(part.wire(witness).canonical().contains("\"kind\":\"type\""));
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    let mut forged = result.nodes.clone();
    let Some(Payload::Construction(value)) = &mut forged[index].payload else {
        panic!()
    };
    let D::Comparison(Part::RelationSource(data)) = &mut value.data else {
        panic!()
    };
    let relation_sources::Kind::Domain { finite, .. } = &mut data.kind else {
        panic!()
    };
    *finite = true;
    assert!(rebuild_for_origin_and_support_recheck(&result, &forged).is_err());
}

#[test]
fn a_finite_prefix_keeps_its_refutation_when_other_prefixes_have_nonfinite_domains() {
    partial_domain_keeps_known_failure(true, "path(e)=identity(source(path(e)))", "comparison");
}

#[test]
fn a_complete_snapshot_keeps_its_refutation_when_another_owned_domain_is_missing() {
    partial_domain_keeps_known_failure(false, "path(e)=identity(source(path(e)))", "comparison");
}

#[test]
fn a_complete_snapshot_keeps_its_path_failure_when_another_owned_domain_is_missing() {
    partial_domain_keeps_known_failure(
        false,
        "then(path(e),path(e))=then(path(e),path(e))",
        "evaluation",
    );
}

#[test]
fn actual_endpoint_and_reading_mismatches_are_comparison_conditions() {
    let endpoint = evaluate_observed_bytes(
        inputs(""),
        &[
            E,
            fixture::F,
            "compared=compare($e.value,to=$f.value,kind=relation)",
        ],
        &mut Control::unlimited(),
    )
    .unwrap();
    let reading = evaluate_observed_bytes(
        fixture::visibility_input(),
        &[
            "one=evaluate(Reservations.route,e=@v/e)",
            "two=evaluate(Alternative.common,e=@v/e)",
            "compared=compare($one.value,to=$two.value,kind=relation)",
        ],
        &mut Control::unlimited(),
    )
    .unwrap();
    for result in [endpoint, reading] {
        assert_eq!(result.answers[0].status, Decision::Established);
        assert_eq!(result.answers[1].status, Decision::Established);
        assert_eq!(
            result.answers[2].status,
            Decision::Refuted,
            "{:?}",
            result.issues
        );
        assert!(!result.answers[2].outputs.contains_key("comparison"));
        assert!(result.answers[2].reasons.iter().any(|reason| matches!(
            reason.kind,
            ReasonKind::ConditionFailed {
                construction: "comparison",
                ..
            }
        )));
        assert!(
            result
                .issues
                .iter()
                .all(|reason| matches!(reason.kind, ReasonKind::ConditionFailed { .. })),
            "{:?}",
            result.issues
        );
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    }
}

#[test]
fn public_relation_stops_keep_prior_values_and_only_finished_sealed_comparisons() {
    let script = "relation stable(e:Hop):path(e)=path(e);";
    let qs = [
        E,
        ALIAS,
        "compared=compare($e.value,to=$alias.value,kind=relation)",
    ];
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let mut probe = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::NativeResultNode {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    let normal = evaluate_observed_bytes(inputs(script), &qs, &mut probe).unwrap();
    assert_eq!(normal.answers[2].status, Decision::Refuted);
    let total = count.get();
    assert!(total > 20);
    for at in [1, total - 3] {
        for mode in 0..4 {
            let (mut control, count) = stopping(at, mode, Checkpoint::NativeResultNode);
            let prepared =
                crate::observed::prepare_observed(inputs(script), &qs, &mut Control::unlimited())
                    .unwrap();
            let result = evaluate_observed(prepared, &mut control).unwrap();
            assert_eq!(result.status(), "interrupted");
            assert_eq!(result.answers[..2], normal.answers[..2]);
            assert_eq!(result.answers[2].outputs.contains_key("comparison"), at > 1);
            if at > 1 {
                assert_eq!(result.answers[2].status, Decision::Refuted);
                assert_eq!(result.answers[2].evidence.len(), 2);
            }
            rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
            assert_eq!(count.get(), at);
            assert!(control.checkpoint(Checkpoint::NativeResultNode).is_err());
            assert_eq!(count.get(), at);
        }
    }
}
#[test]
fn reconstructed_relation_proofs_reject_payload_plan_scope_and_source_family_forgery() {
    use crate::observed::public_compare::relations::Data;
    let result = public(
        ALIAS_RELATION,
        &[
            E,
            ALIAS,
            "compared=compare($e.value,to=$alias.value,kind=relation)",
        ],
    );
    let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    let env = Environment::with_prepared(result.prepared(), &mut Control::unlimited()).unwrap();
    env.validate_answer(
        &graph,
        &result.prepared().requests().requests()[2],
        &result.answers[2],
    )
    .unwrap();
    let word=graph.nodes.iter().position(|node|matches!(&node.payload,Some(Payload::Construction(value)) if matches!(&value.data,D::Comparison(Part::RelationDerived{data,..}) if matches!(data.as_ref(),Data::Value{value:Scalar::Tuple(values),..} if values.len()==4)))).unwrap();
    let claim = result.answers[2].claim.unwrap().0;
    for mode in 0..10 {
        let index = if mode >= 7 { claim } else { word };
        let mut node = graph.nodes[index].clone();
        match mode {
            0 => node.arguments.clear(),
            1 => node.support.clear(),
            2 => node.scope.readings.clear(),
            3 => node.scope.completions = !node.scope.completions,
            7 => node.judgment.as_mut().unwrap().status = Decision::Refuted,
            8 => node.evidence.clear(),
            _ => {
                let Some(Payload::Construction(value)) = &mut node.payload else {
                    panic!()
                };
                if mode == 9 {
                    let Witness::Compare(w) = &mut value.witness else {
                        panic!()
                    };
                    let w = std::sync::Arc::make_mut(w);
                    w.scope.completions = !w.scope.completions;
                    node.scope = w.scope.clone();
                } else {
                    let D::Comparison(Part::RelationDerived { index, data }) = &mut value.data
                    else {
                        panic!()
                    };
                    match data.as_mut() {
                        Data::Value {
                            value: Scalar::Tuple(values),
                            arguments,
                        } => match mode {
                            4 => values[3] = Scalar::Z(999.into()),
                            5 => arguments.clear(),
                            _ => values.swap(0, 1),
                        },
                        _ => panic!(),
                    }
                    if mode == 6 {
                        let Witness::Compare(w) = &mut value.witness else {
                            panic!()
                        };
                        let w = std::sync::Arc::make_mut(w);
                        std::sync::Arc::make_mut(w.relation_plan.as_mut().unwrap()).nodes[*index] =
                            data.as_ref().clone();
                    }
                }
            }
        }
        assert!(
            env.recheck_node(&graph, &node, index).is_err(),
            "forgery {mode}"
        );
    }
    let source=graph.nodes.iter().position(|node|matches!(&node.payload,Some(Payload::Construction(value)) if matches!(value.data,D::Comparison(Part::RelationSource(_))))).unwrap();
    let mut forged = graph.nodes[source].clone();
    let Some(Payload::Construction(value)) = &mut forged.payload else {
        panic!()
    };
    let Witness::Compare(w) = &mut value.witness else {
        panic!()
    };
    let family = std::sync::Arc::make_mut(
        std::sync::Arc::make_mut(w)
            .relation_family
            .as_mut()
            .unwrap(),
    );
    family.table.instances[0].state =
        crate::observed::environment::relation_instances::RelationState::Pending;
    assert!(env.recheck_node(&graph, &forged, source).is_err());
}

#[test]
fn an_empty_word_and_an_identity_action_have_different_relation_classes() {
    let result = public(
        "",
        &[
            "edge=evaluate(Walk.step,e=@v/self)",
            "identityValue=evaluate(Walk.identityAt,x=@v/p)",
            "relationValue=compare($edge.value,to=$identityValue.value,kind=relation)",
            "actionValue=compare($edge.value,to=$identityValue.value,kind=action)",
        ],
    );
    assert_eq!(result.answers[2].status, Decision::Refuted);
    assert_eq!(result.answers[3].status, Decision::Established);
}
#[test]
fn relation_kind_is_a_fixed_keyword_while_identifiers_and_private_projections_stay_rejected() {
    for asks in [
        vec!["relation=evaluate(Walk.step,e=@v/e)"],
        vec![
            E,
            "compared=compare($e.value,to=$e.value,kind=relation,along=$e.value)",
        ],
        vec![
            E,
            fixture::F,
            fixture::C,
            "compared=compare($c.value,to=$e.value,kind=relation)",
        ],
    ] {
        assert!(
            crate::observed::prepare_observed(inputs(""), &asks, &mut Control::unlimited())
                .is_err()
        );
    }
}

#[test]
fn a_relation_with_matching_endpoints_still_checks_every_actual_action_image() {
    let result = evaluate_observed_bytes(
        relation_fixture::composition_refutation(),
        &[
            E,
            fixture::F,
            fixture::C,
            "direct=evaluate(Walk.step,e=@v/different)",
            "compared=compare($c.operation,to=$direct.value,kind=relation)",
        ],
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(
        result.answers[4].status,
        Decision::Refuted,
        "{:?}",
        result.issues
    );
    assert!(!result.answers[4].outputs.contains_key("comparison"));
    assert!(
        result
            .issues
            .iter()
            .all(|reason| matches!(reason.kind, ReasonKind::ConditionFailed { .. })),
        "{:?}",
        result.issues
    );
    let counter = &result.nodes[result.answers[4].evidence[0].0];
    let Some(Payload::Construction(value)) = &counter.payload else {
        panic!()
    };
    let D::Comparison(Part::RelationDerived { data, .. }) = &value.data else {
        panic!()
    };
    let crate::observed::public_compare::relations::Data::FailureEvidence { facts, .. } =
        data.as_ref()
    else {
        panic!()
    };
    assert_eq!(
        facts
            .iter()
            .map(|fact| (
                fact.snapshot.as_str(),
                fact.subject.as_str(),
                fact.field.as_deref(),
                fact.atom.as_deref()
            ))
            .collect::<Vec<_>>(),
        vec![
            ("v", "q", None, None),
            ("v", "r", None, None),
            ("v", "q", None, None)
        ]
    );
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
}

#[test]
fn the_missing_guard_can_change_the_actual_relation_decision_in_both_completions() {
    for (value, expected) in [(false, Decision::Refuted), (true, Decision::Established)] {
        let result = evaluate_observed_bytes(
            relation_fixture::known_guard(value),
            &[
                E,
                ALIAS,
                "compared=compare($e.value,to=$alias.value,kind=relation)",
            ],
            &mut Control::unlimited(),
        )
        .unwrap();
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        assert_eq!(result.answers[2].status, expected);
        assert!(result.issues.is_empty());
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    }
}
#[test]
fn quantified_original_guard_keeps_its_actual_domain_in_the_comparison_scope() {
    let result = public(
        "relation quantified(e:Hop) when (forall flag:Bool . flag or not flag):lexical(e)=path(e);",
        &[
            E,
            ALIAS,
            "compared=compare($e.value,to=$alias.value,kind=relation)",
        ],
    );
    assert_eq!(result.answers[2].status, Decision::Refuted);
    assert!(
        result.answers[2]
            .scope
            .quantifiers
            .iter()
            .any(|q| q.name == "flag" && q.domain.is_some())
    );
}
fn path_names(value: &Scalar) -> Vec<(String, String, String)> {
    let Scalar::Path(path) = value else { panic!() };
    let Some(step) = &path.step else {
        return vec![];
    };
    std::iter::once(&step.generator)
        .chain(&step.word_tail)
        .map(|value| match value {
            Scalar::Subject {
                snapshot,
                subject,
                entity,
            } => (snapshot.clone(), subject.clone(), entity.clone()),
            _ => panic!(),
        })
        .collect()
}
fn certificate_names(value: &Scalar) -> Vec<(String, String, String)> {
    let Scalar::Tuple(values) = value else {
        panic!()
    };
    let Scalar::List { items, .. } = &values[2] else {
        panic!()
    };
    items
        .iter()
        .map(|value| {
            let Scalar::Tuple(names) = value else {
                panic!()
            };
            let [
                Scalar::Text(snapshot),
                Scalar::Text(subject),
                Scalar::Text(entity),
            ] = names.as_slice()
            else {
                panic!()
            };
            (snapshot.clone(), subject.clone(), entity.clone())
        })
        .collect()
}
fn relation_data(
    graph: &Graph,
    reference: NodeRef,
) -> Option<&crate::observed::public_compare::relations::Data> {
    let Payload::Construction(value) = graph.get(reference).unwrap().payload.as_ref()? else {
        return None;
    };
    let D::Comparison(Part::RelationDerived { data, .. }) = &value.data else {
        return None;
    };
    Some(data)
}
#[test]
fn both_orientations_of_a_public_derivation_agree_with_the_original_binding_and_word_context() {
    use crate::observed::public_compare::relations::Data;
    let result = public(
        ALIAS_RELATION,
        &[
            E,
            ALIAS,
            "forward=compare($e.value,to=$alias.value,kind=relation)",
            "backward=compare($alias.value,to=$e.value,kind=relation)",
        ],
    );
    let mut graph = Graph::new(&Control::unlimited());
    graph.nodes = result.nodes.clone().into();
    let mut reversed = false;
    for answer in &result.answers[2..] {
        assert_eq!(answer.status, Decision::Established);
        let Some(Data::Normalization {
            before,
            after,
            steps,
            ..
        }) = relation_data(&graph, answer.evidence[1])
        else {
            panic!()
        };
        let mut current = path_names(graph.scalar(*before).unwrap());
        for step in steps {
            let Some(Data::Rewrite {
                left,
                right,
                arguments,
            }) = relation_data(&graph, *step)
            else {
                panic!()
            };
            reversed |= arguments
                .iter()
                .any(|r| matches!(relation_data(&graph, *r), Some(Data::Rewrite { .. })));
            let originals = arguments
                .iter()
                .filter_map(|reference| match &graph.get(*reference).unwrap().payload {
                    Some(Payload::Evaluation {
                        value: Some(value), ..
                    }) if matches!(
                        graph.get(*reference).unwrap().ty,
                        NodeType::Evaluation(Type::Path(..))
                    ) =>
                    {
                        Some(*value)
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(originals.len(), 2);
            let metadata = arguments
                .iter()
                .filter_map(|reference| match relation_data(&graph, *reference) {
                    Some(Data::Value {
                        value: Scalar::Tuple(values),
                        ..
                    }) if values.len() == 2 => Some(values),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(metadata.len(), 1);
            let [Scalar::Bool(right_to_left), Scalar::Z(offset)] = metadata[0].as_slice() else {
                panic!()
            };
            assert_eq!(
                (*left, *right),
                if *right_to_left {
                    (originals[1], originals[0])
                } else {
                    (originals[0], originals[1])
                }
            );
            let words = arguments
                .iter()
                .filter_map(|reference| match relation_data(&graph, *reference) {
                    Some(Data::Value {
                        value: word @ Scalar::Tuple(values),
                        ..
                    }) if values.len() == 4 => Some(certificate_names(word)),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(words.len(), 2);
            assert_eq!(words[0], current);
            let offset = offset.to_string().parse::<usize>().unwrap();
            let from = path_names(graph.scalar(*left).unwrap());
            let to = path_names(graph.scalar(*right).unwrap());
            assert_eq!(current[offset..offset + from.len()], from);
            current.splice(offset..offset + from.len(), to);
            assert_eq!(words[1], current);
        }
        assert_eq!(current, path_names(graph.scalar(*after).unwrap()));
    }
    assert!(reversed);
}
