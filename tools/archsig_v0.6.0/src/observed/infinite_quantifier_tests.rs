use super::*;
use crate::law::ast::{QuantDomain, QuantKind, QuantSplit};

const DECLARATIONS: &str = "view seed():Z=1; law required prior():1=2; view keep(x:Bool):Bool=x;";
const ASKS: &[&str] = &[
    "seed=evaluate(Calc.seed)",
    "prior=check(Calc.prior)",
    "v=evaluate(Calc.caller,s=@v/sample)",
    "later=evaluate(Calc.keep,x=$v.value)",
];
fn input(omitted: &[&str], body: &str) -> InputSources {
    numeric_recheck_fixture(omitted, &format!("{DECLARATIONS}{body}"))
}
fn run(omitted: &[&str], body: &str) -> ObservedEvaluation {
    let inputs = input(omitted, body);
    let result = evaluate_observed_bytes(inputs.clone(), ASKS, &mut named_call_quiet()).unwrap();
    assert_eq!(result.prepared.inputs().sources(), &inputs);
    assert_eq!(result.status(), "partial", "{body}: {:?}", result.issues);
    assert_eq!(result.answers[0].status, Decision::Established);
    assert_eq!(
        data_scalar_at(&result, result.answers[0].outputs["value"].0),
        &Scalar::Z(1.into())
    );
    assert_eq!(result.answers[1].status, Decision::Refuted);
    assert!(result.answers[1].claim.is_some() && !result.answers[1].evidence.is_empty());
    assert_eq!(result.answers[2].status, Decision::Undetermined);
    assert!(!result.answers[2].outputs.contains_key("value"));
    assert_eq!(result.answers[3].status, Decision::Undetermined);
    assert!(result.answers[3].outputs.is_empty());
    assert!(result.answers[3].reasons.iter().any(|reason| matches!(&reason.kind, ReasonKind::DependencyBlocked { request, .. } if request == "v")));
    for reason in &result.answers[2].reasons {
        assert!(
            result.answers[3]
                .reasons
                .iter()
                .any(|other| reason.wire() == other.wire())
        );
    }
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    result
}
fn quantified(result: &ObservedEvaluation) -> (usize, usize, usize) {
    let reason = result
        .answers
        .iter()
        .find(|answer| answer.id == "v")
        .unwrap()
        .reasons
        .iter()
        .find(|reason| matches!(reason.kind, ReasonKind::UnsupportedAlgorithm { .. }))
        .unwrap();
    let [source] = reason.dependencies.as_slice() else {
        panic!("元量化source")
    };
    let whole = result.nodes.iter().rposition(|node| matches!(&node.payload,Some(Payload::Evaluation { expression, value:None, .. }) if expression == source)).unwrap();
    let domain = result
        .nodes
        .iter()
        .position(|node| {
            matches!(&node.payload, Some(Payload::TypeDomain { .. })) && node.arguments == [*source]
        })
        .unwrap();
    (source.0, domain, whole)
}
fn check_quantifiers(result: &ObservedEvaluation) {
    let law = result.prepared.inputs().law();
    let original = result.prepared.inputs().sources().law().bytes();
    let (source, _, whole) = quantified(result);
    let Some(Payload::Expression {
        location: Location::Law { span },
        ..
    }) = &result.nodes[source].payload
    else {
        panic!()
    };
    assert!(
        std::str::from_utf8(&original[span.0..span.1])
            .unwrap()
            .contains("exists")
    );
    let scope = &result.nodes[whole].scope;
    assert!(scope.assignments);
    let mut exists = false;
    for descriptor in &scope.quantifiers {
        let (id, kind, var) = law
            .exprs
            .iter()
            .enumerate()
            .find_map(|(id, expression)| match &expression.kind {
                ExprKind::Quant {
                    kind,
                    var,
                    split:
                        QuantSplit::Fixed {
                            domain: QuantDomain::Type(_),
                            ..
                        },
                } if var.span == descriptor.occurrence => Some((id, *kind, var)),
                _ => None,
            })
            .unwrap();
        assert_eq!(descriptor.kind, kind);
        assert_eq!(descriptor.name, var.name);
        assert_eq!(Some(&descriptor.ty), law.quantifier_types[id].as_ref());
        // callerの静的分析で得たdescriptorとは別に、実calleeの全域を要求する。
        let Some(domain) = descriptor.domain else {
            assert!(scope.quantifiers.iter().any(|actual| actual.occurrence
                == descriptor.occurrence
                && actual.kind == descriptor.kind
                && actual.ty == descriptor.ty
                && actual.domain.is_some()));
            continue;
        };
        assert!(domain.0 < whole);
        assert_eq!(result.nodes[domain.0].ty, NodeType::Domain);
        assert!(
            matches!(&result.nodes[domain.0].payload,Some(Payload::TypeDomain {ty}) if ty==&descriptor.ty)
        );
        assert!(
            matches!(&result.nodes[domain.0].rule,Rule::Input {kind:"law",location:Location::Law {span}} if *span==var.span)
        );
        assert_eq!(descriptor.context, Some(result.contexts[domain.0]));
        exists |= kind == QuantKind::Exists;
        // bodyのbinder出現・元式は型付きSourceで残る。
        let ExprKind::Quant {
            split: QuantSplit::Fixed { body, .. },
            ..
        } = &law.exprs[id].kind
        else {
            panic!()
        };
        assert!(result.nodes.iter().any(|node| matches!(&node.payload,Some(Payload::Expression {location:Location::Law {span},..}) if *span==law.exprs[*body].span)));
    }
    assert!(exists);
    assert!(result.answers.iter().find(|answer|answer.id=="v").unwrap().reasons.iter().any(|reason| matches!(&reason.kind,ReasonKind::UnsupportedAlgorithm {operand_types, method, question:QuestionKind::Evaluate} if !operand_types.is_empty() && !method.is_empty())));
}

#[test]
fn infinite_exists_callee_returns_typed_undetermined_instead_of_early_error() {
    let inputs = numeric_recheck_fixture(
        &[],
        "view unsupported(s:Sample):Bool=exists item:Z.item*item=0; view caller(s:Sample):Bool=unsupported(s);",
    );
    let result = evaluate_observed_bytes(
        inputs,
        &["v=evaluate(Calc.caller,s=@v/sample)"],
        &mut named_call_quiet(),
    )
    .expect("有効な無限域の算法非対応は型付き未決回答を返す");
    assert_eq!(result.status(), "partial");
    assert_eq!(result.answers[0].status, Decision::Undetermined);
    assert!(
        result.answers[0]
            .reasons
            .iter()
            .any(|reason| matches!(reason.kind, ReasonKind::UnsupportedAlgorithm { .. }))
    );
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    check_quantifiers(&result);
}

#[test]
fn infinite_numeric_exists_keeps_original_kind_domains_and_call_lexical_context() {
    for expression in [
        "exists item:Z.item=0",
        "exists item:Q.item=rat(0,1)",
        "exists item:Z.item*item=0",
        "exists item:Q.item*item=rat(0,1)",
        "forall z:Z.exists item:Z.item*item=z",
        "exists item:Z.forall z:Z.item*item=z",
        "let n=rat(1,2) in exists item:Q.item*item=n",
        "forall z:Z.if true then (exists item:Z.item*item=z) else false",
    ] {
        let body = format!(
            "view inner(s:Sample):Bool={expression};view middle(s:Sample):Bool=inner(s);view caller(s:Sample):Bool=middle(s);"
        );
        let result = run(&[], &body);
        check_quantifiers(&result);
        let (source, _, _) = quantified(&result);
        let context = result.contexts[source];
        let frame = &result.frames[context.frame.expect("callee実frame")];
        assert!(
            frame.caller.frame.is_some(),
            "二段呼出しの元callerを保持する"
        );
    }
}

#[test]
fn infinite_exists_preserves_missing_slot_and_independent_refutation() {
    let result = run(
        &["q"],
        "view caller(s:Sample):Bool=exists item:Q.item*item=s.q;",
    );
    check_quantifiers(&result);
    let reason = result.answers[2]
        .reasons
        .iter()
        .find(|r| matches!(r.kind, ReasonKind::Missing))
        .unwrap();
    assert_eq!(reason.missing.len(), 1);
    assert_eq!(reason.missing[0].snapshot, "v");
    assert_eq!(reason.missing[0].subject, "sample");
    assert_eq!(reason.missing[0].field.as_deref(), Some("Numeric.Sample.q"));
    for source in &reason.dependencies {
        assert!(
            matches!(&result.nodes[source.0].payload,Some(Payload::Expression { location:Location::Law {span},..}) if &result.prepared.inputs().sources().law().bytes()[span.0..span.1]==b"s.q")
        );
    }
}

#[test]
fn finite_and_affine_quantifiers_and_short_circuit_still_decide() {
    for (expression, expected) in [
        ("forall item:Bool.item", false),
        ("exists item:Bool.item", true),
        ("forall item:Z.item+1=item+1", true),
        ("forall item:Z.item+1=item+2", false),
        ("forall item:Q.item+rat(1,2)+rat(1,2)=item+1", true),
        ("forall item:Q.item+rat(1,2)+rat(1,2)=item+2", false),
        ("exists item:Z.true", true),
        ("exists item:Q.false", false),
        ("false and (exists item:Z.item*item=0)", false),
        ("true or (exists item:Z.item*item=0)", true),
        ("exists item in list<Z>[2,3].item*item=4", true),
    ] {
        let result = evaluate_observed_bytes(
            input(&[], &format!("view caller(s:Sample):Bool={expression};")),
            &["v=evaluate(Calc.caller,s=@v/sample)"],
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_eq!(
            result.status(),
            "complete",
            "{expression}: {:?}",
            result.issues
        );
        assert_eq!(
            data_scalar_at(&result, result.answers[0].outputs["value"].0),
            &Scalar::Bool(expected),
            "{expression}"
        );
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    }
}

#[test]
fn infinite_exists_domain_scope_source_and_reason_mutations_are_rejected() {
    let result = run(&[], "view caller(s:Sample):Bool=exists item:Z.item*item=0;");
    let (source, domain, whole) = quantified(&result);
    completion_mutation(&result, domain, |nodes| {
        nodes[domain].payload = Some(Payload::TypeDomain { ty: Type::Q });
    });
    completion_mutation(&result, whole, |nodes| {
        let q = nodes[whole]
            .scope
            .quantifiers
            .iter_mut()
            .find(|q| q.kind == QuantKind::Exists)
            .unwrap();
        q.kind = QuantKind::Forall;
    });
    completion_mutation(&result, whole, |nodes| {
        nodes[whole]
            .reasons
            .retain(|r| !matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }));
    });
    completion_mutation(&result, source, |nodes| {
        let Some(Payload::Expression {
            location: Location::Law { span },
            ..
        }) = &mut nodes[source].payload
        else {
            panic!()
        };
        span.1 -= 1;
    });
    let mut graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    let environment = Environment::with_requests(
        result.prepared.inputs(),
        result.prepared.requests().requests(),
        &mut named_call_quiet(),
    )
    .unwrap();
    for variant in 0..3 {
        environment
            .recheck_node(&graph, &graph.nodes[whole], whole)
            .unwrap();
        match variant {
            0 => graph.nodes[domain].payload = Some(Payload::TypeDomain { ty: Type::Q }),
            1 => graph.contexts[domain].request = 0,
            2 => graph.nodes[whole].reasons.clear(),
            _ => unreachable!(),
        }
        assert!(matches!(
            environment.recheck_node(&graph, &graph.nodes[whole], whole),
            Err(ValidationFailure::Internal(_))
        ));
        graph.nodes = result.nodes.clone();
        graph.contexts = result.contexts.clone();
        environment
            .recheck_node(&graph, &graph.nodes[whole], whole)
            .unwrap();
    }
}

#[test]
fn infinite_exists_law_retains_undetermined_proposition_and_rechecks_original_reasons() {
    let asks = [ASKS[0], ASKS[1], "v=check(Calc.existential,s=@v/sample)"];
    let result = evaluate_observed_bytes(
        input(
            &[],
            "law required existential(s:Sample):exists item:Z.item*item=0;",
        ),
        &asks,
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "partial");
    assert_eq!(result.answers[1].status, Decision::Refuted);
    let answer = &result.answers[2];
    assert_eq!(answer.status, Decision::Undetermined);
    let claim = answer.claim.expect("未決命題も保持する");
    assert_eq!(result.nodes[claim.0].ty, NodeType::Proposition);
    assert_eq!(
        result.nodes[claim.0].judgment.as_ref().unwrap().status,
        answer.status
    );
    assert_eq!(result.nodes[claim.0].evidence, answer.evidence);
    assert!(answer.reasons.iter().any(|r| matches!(
        r.kind,
        ReasonKind::UnsupportedAlgorithm {
            question: QuestionKind::Check,
            ..
        }
    )));
    let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    let environment = Environment::with_requests(
        result.prepared.inputs(),
        result.prepared.requests().requests(),
        &mut named_call_quiet(),
    )
    .unwrap();
    let request = &result.prepared.requests().requests()[2];
    environment
        .validate_answer(&graph, request, answer)
        .unwrap();
    let mut changed = answer.clone();
    changed
        .reasons
        .retain(|r| !matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }));
    assert_ne!(&changed, answer);
    assert!(matches!(
        environment.validate_answer(&graph, request, &changed),
        Err(ValidationFailure::Internal(_))
    ));
    environment
        .validate_answer(&graph, request, answer)
        .unwrap();
}

#[test]
fn infinite_exists_preserves_mathematics_and_current_observation_provenance() {
    let first = input(
        &[],
        "view caller(s:Sample):Bool=exists item:Q.item*item=s.q;",
    );
    let map = String::from_utf8(first.archmap().bytes().to_vec()).unwrap();
    assert_eq!(map.matches("\"revision\":\"r1\"").count(), 1);
    assert_eq!(map.matches("\"span\":[2,5]").count(), 1);
    let second = InputSources::from_bytes(
        first
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        first.law().bytes().to_vec(),
        map.replace("\"revision\":\"r1\"", "\"revision\":\"r2\"")
            .replace("\"span\":[2,5]", "\"span\":[12,15]")
            .into_bytes(),
    );
    let mut wires = Vec::new();
    for (input, revision, span) in [(first, "r1", (2, 5)), (second, "r2", (12, 15))] {
        let result = evaluate_observed_bytes(input.clone(), ASKS, &mut named_call_quiet()).unwrap();
        assert_eq!(result.status(), "partial");
        assert_eq!(result.prepared.inputs().sources(), &input);
        check_quantifiers(&result);
        let (_, _, whole) = quantified(&result);
        let support = &result.nodes[whole].support;
        let fact = support
            .iter()
            .find(|f| f.field.as_deref() == Some("Numeric.Sample.q"))
            .expect("既知qの支持");
        assert_eq!(fact.atom.as_deref(), Some("q"));
        let checked = result.prepared.inputs().archmap();
        let field = &checked.snapshots[0].subjects[0]
            .fields
            .iter()
            .find(|f| f.name == "Numeric.Sample.q")
            .unwrap();
        let crate::archmap::Slot::Known { origin, atom, .. } = &field.slot else {
            panic!()
        };
        assert_eq!(Some(atom), fact.atom.as_ref());
        let origin = checked.origins.iter().find(|o| &o.id == origin).unwrap();
        assert!(!origin.locations.is_empty());
        for location in &origin.locations {
            let source = checked
                .sources
                .iter()
                .find(|s| s.id == location.source)
                .unwrap();
            assert_eq!(source.revision, revision);
            assert_eq!(location.span, Some(span));
        }
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let Json::Obj(ref object) = result.wire() else {
            panic!()
        };
        wires.push((
            object["inputs"].clone(),
            object["nodes"].clone(),
            object["answers"].clone(),
        ));
    }
    assert_ne!(wires[0].0, wires[1].0);
    assert_eq!(wires[0].1, wires[1].1);
    assert_eq!(wires[0].2, wires[1].2);
}

fn stop(fresh_recheck: bool) {
    use std::{cell::Cell, rc::Rc};
    let body = "view caller(s:Sample):Bool=exists item:Z.item*item=0;";
    let inputs = input(&[], body);
    let normal = evaluate_observed_bytes(inputs.clone(), ASKS, &mut named_call_quiet()).unwrap();
    assert_eq!(normal.status(), "partial");
    let (source, _, _) = quantified(&normal);
    let span = match &normal.nodes[source].payload {
        Some(Payload::Expression {
            location: Location::Law { span },
            ..
        }) => *span,
        _ => panic!(),
    };
    let (limits, usage, expected) =
        reservations_private_stop_usage(if fresh_recheck { 2 } else { 0 });
    let armed = Rc::new(Cell::new(false));
    let phase = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(0));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut control = Control::new(limits, move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            usage
        } else {
            Default::default()
        }
    });
    let prepared = prepare_observed(inputs, ASKS, &mut control).unwrap();
    let mut copy = control.clone();
    let stopped = evaluate_observed_with_validator(
        prepared,
        &mut control,
        |environment, graph, request, answer| {
            environment.validate_answer(graph, request, answer)?;
            if request.id == "prior" {
                let (a, ph, s) = (armed.clone(), phase.clone(), seen.clone());
                data::observe_iterations(move |at, context, operation, index| {
                    if at == span
                        && context.request == 2
                        && ((!fresh_recheck && operation == "universal" && index == 0)
                            || (fresh_recheck && ph.get() && operation == "quantifier_kind"))
                    {
                        assert_eq!(s.get(), 0);
                        s.set(1);
                        a.set(true);
                    }
                });
            }
            if fresh_recheck && request.id == "v" {
                let fresh = Environment::with_requests(
                    normal.prepared.inputs(),
                    normal.prepared.requests().requests(),
                    &mut copy,
                )?;
                phase.set(true);
                let result = fresh.validate_answer(graph, request, answer);
                phase.set(false);
                result?;
            }
            Ok(())
        },
    )
    .unwrap();
    data::clear_iteration_observer();
    assert_eq!(seen.get(), 1);
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(control.stop_reason(), Some(expected.clone()));
    assert_eq!(Some(probes.get()), frozen.get());
    assert_eq!(
        format!("{:?}", stopped.nodes),
        format!("{:?}", &normal.nodes[..stopped.nodes.len()])
    );
    assert_eq!(stopped.contexts, normal.contexts[..stopped.contexts.len()]);
    assert_eq!(&stopped.answers[..2], &normal.answers[..2]);
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    assert!(stopped.answers[1].claim.is_some() && !stopped.answers[1].evidence.is_empty());
    for index in 2..4 {
        if fresh_recheck && index == 2 {
            assert_eq!(
                stopped.answers[index].outputs,
                normal.answers[index].outputs
            );
            assert_eq!(stopped.answers[index].claim, normal.answers[index].claim);
            assert_eq!(
                stopped.answers[index].evidence,
                normal.answers[index].evidence
            );
        } else {
            assert!(stopped.answers[index].outputs.is_empty());
        }
        assert_eq!(stopped.answers[index].status, Decision::Undetermined);
        let reason = stopped.answers[index]
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(actual)if actual==&expected))
            .unwrap();
        assert_eq!(reason.request, stopped.answers[index].id);
        let (Json::Obj(ref actual), Json::Obj(ref wanted)) = (reason.wire(), expected.wire())
        else {
            panic!()
        };
        assert_eq!(actual["details"], wanted["details"]);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn infinite_exists_actual_domain_stop_keeps_verified_prefix_and_prior_answers() {
    stop(false)
}
#[test]
fn infinite_exists_fresh_recheck_stop_keeps_verified_current_and_freezes() {
    stop(true)
}
