fn owned_private_fixture(body: &str, omit: Option<&str>, false_p: bool) -> InputSources {
    let definition = include_bytes!("../../tests/fixtures/reservations.atoms.json");
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Reservations {{ use vocabulary Reservations version \"1\" digest \"sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff\"; {body} }}"
    );
    let mut map = include_str!("../../tests/fixtures/reservations.archmap.json")
        .lines()
        .filter(|line| !omit.is_some_and(|id| line.contains(&format!("\"id\": \"{id}\""))))
        .map(|line| {
            if false_p && line.contains("\"id\": \"p-free\"") {
                line.replace("\"value\": \"2\"", "\"value\": \"0\"")
            } else {
                line.into()
            }
        })
        .collect::<Vec<String>>()
        .join("\n");
    map = map.replace(
        "\"subjects\": [",
        "\"subjects\": [{\"id\":\"Z\",\"type\":\"Reservations.System\",\"origin\":\"model\"},",
    );
    let suffix = "  }]\n}";
    assert!(map.ends_with(suffix));
    map.truncate(map.len() - suffix.len());
    map.push_str(r#"  },{"id":"w","origin":"model","subjects":[{"id":"A","type":"Reservations.System","origin":"model"},{"id":"p","type":"Reservations.State","origin":"model"}],"atoms":[{"id":"p-owner","subject":"p","field":"Reservations.State.owner","value":["w","A"],"origin":"model"},{"id":"p-free","subject":"p","field":"Reservations.State.free","value":"7","origin":"model"},{"id":"p-held","subject":"p","field":"Reservations.State.held","value":"0","origin":"model"}]}]}"#);
    InputSources::from_bytes(
        vec![definition.to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
fn owned_private_example(
    body: &str,
    asks: &[&str],
    omit: Option<&str>,
    false_p: bool,
) -> ObservedEvaluation {
    let result = evaluate_observed_bytes(
        owned_private_fixture(body, omit, false_p),
        asks,
        &mut quiet(),
    )
    .unwrap();
    assert_ne!(result.status(), "error", "{:?}", result.issues);
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    result
}
fn owned_private_evaluations(result: &ObservedEvaluation) -> Vec<usize> {
    result
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, node)| {
            let Some(Payload::Evaluation { expression, .. }) = &node.payload else {
                return None;
            };
            let Some(Payload::Expression {
                location: Location::Law { span },
                ..
            }) = &result.nodes[expression.0].payload
            else {
                return None;
            };
            result
                .prepared
                .inputs()
                .law()
                .exprs()
                .iter()
                .any(|e| e.span == *span && matches!(e.kind, ExprKind::Family { .. }))
                .then_some(i)
        })
        .collect()
}
fn owned_private_parts(
    result: &ObservedEvaluation,
    evaluation: usize,
) -> (usize, Option<usize>, usize) {
    let Some(Payload::Evaluation {
        expression,
        value,
        parts,
        ..
    }) = &result.nodes[evaluation].payload
    else {
        panic!("Family evaluation")
    };
    assert_eq!(parts.len(), 1);
    assert_eq!(parts[0].children.len(), 1);
    (expression.0, value.map(|v| v.0), parts[0].children[0].0)
}
const OWNED_VIEW: &str = "view states(a:System):Set<State> =State[a];";

#[test]
fn owned_expression_family_in_domain_exhaustion_missing_and_counterexample_recheck() {
    let body = "law required okay(a:System):forall s in State[a] . s.free>0;";
    let normal = owned_private_example(body, &["all=check(Reservations.okay,a=@v/A)"], None, false);
    assert_eq!(normal.answers[0].status, Decision::Established);
    let proof = normal
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            matches!(
                n.payload,
                Some(Payload::FiniteExhaustion { checked: 2, .. })
            )
            .then_some(i)
        })
        .unwrap();
    let Some(Payload::FiniteExhaustion { domain, .. }) = &normal.nodes[proof].payload else {
        unreachable!()
    };
    let domain = domain.0;
    completion_mutation(&normal, domain, |nodes| {
        let Some(Payload::Domain { elements, .. }) = &mut nodes[domain].payload else {
            unreachable!()
        };
        elements.pop();
        nodes[domain].arguments.pop();
    });
    completion_mutation(&normal, domain, |nodes| {
        let Some(Payload::Domain { elements, .. }) = &mut nodes[domain].payload else {
            unreachable!()
        };
        let extra = elements[0];
        elements.push(extra);
        nodes[domain].arguments.push(extra);
    });
    completion_mutation(&normal, proof, |nodes| {
        let Some(Payload::FiniteExhaustion { checked, .. }) = &mut nodes[proof].payload else {
            unreachable!()
        };
        *checked += 1;
    });
    let result = owned_private_example(
        body,
        &["all=check(Reservations.okay,a=@v/A)"],
        Some("q-free"),
        true,
    );
    assert_eq!(result.answers[0].status, Decision::Refuted);
    assert!(
        result.answers[0]
            .reasons
            .iter()
            .flat_map(|r| &r.missing)
            .any(|f| f.subject == "q" && f.field.as_deref() == Some("Reservations.State.free"))
    );
    let counter = result
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| matches!(n.payload, Some(Payload::Counterexample { .. })).then_some(i))
        .unwrap();
    completion_mutation(&result, counter, |nodes| {
        let Some(Payload::Counterexample { facts, .. }) = &mut nodes[counter].payload else {
            unreachable!()
        };
        facts.pop();
    });
}

#[test]
fn owned_expression_family_unknown_owner_and_candidate_keep_missing_source_and_all_completions() {
    for (body, ask, omit, subject, field) in [(
        OWNED_VIEW,
        "value=evaluate(Reservations.states,a=@v/A)",
        "q-owner",
        "q",
        "Reservations.State.owner",
    )] {
        let result = owned_private_example(body, &[ask], Some(omit), false);
        assert_eq!(result.status(), "complete");
        assert_eq!(result.answers[0].status, Decision::Established);
        let value = result.answers[0].outputs["value"];
        let Some(Payload::Scalar(Scalar::Set { element, items })) = &result.nodes[value.0].payload
        else {
            panic!()
        };
        assert_eq!(element, &Type::Ref("Reservations.State".into()));
        assert_eq!(
            items,
            &vec![
                Scalar::Subject {
                    snapshot: "v".into(),
                    subject: "p".into(),
                    entity: "Reservations.State".into()
                },
                Scalar::Subject {
                    snapshot: "v".into(),
                    subject: "q".into(),
                    entity: "Reservations.State".into()
                },
            ]
        );
        assert!(result.answers[0].scope.completions);
        assert!(!result.answers[0].reasons.iter().any(|r|matches!(&r.kind,ReasonKind::UnsupportedAlgorithm {method,..} if method=="unresolved_owned_expression_family")));
        assert!(
            result.answers[0]
                .reasons
                .iter()
                .flat_map(|r| &r.missing)
                .any(|f| f.snapshot == "v"
                    && f.subject == subject
                    && f.field.as_deref() == Some(field))
        );
        let evaluation = owned_private_evaluations(&result)[0];
        let (source, value, _) = owned_private_parts(&result, evaluation);
        assert!(value.is_none());
        completion_mutation(&result, evaluation, |nodes| {
            nodes[evaluation].reasons.clear();
        });
        completion_mutation(&result, evaluation, |nodes| {
            nodes[evaluation].scope.completions = false;
        });
        completion_mutation(&result, source, |nodes| {
            nodes[source].scope.completions = false;
        });
        let missing = evaluation;
        completion_mutation(&result, missing, |nodes| {
            let reason = nodes[missing]
                .reasons
                .iter_mut()
                .find(|r| !r.missing.is_empty())
                .unwrap();
            reason.missing[0].subject = "p".into();
        });
    }
}

#[test]
fn owned_expression_family_enumeration_cancel_preserves_owner_prefix_and_prior_answers() {
    use std::{cell::Cell, rc::Rc};
    let body = format!(
        "view seed():Unit=unit; law required prior():false; view hole(s:State):Z=s.free; {OWNED_VIEW} law required walk(a:System):forall s in State[a] . s.held>=0;"
    );
    let asks = [
        "seed=evaluate(Reservations.seed)",
        "prior=check(Reservations.prior)",
        "hole=evaluate(Reservations.hole,s=@v/q)",
        "current=evaluate(Reservations.states,a=@v/A)",
        "later=evaluate(Reservations.seed)",
    ];
    let inputs = owned_private_fixture(&body, Some("q-free"), false);
    let mut quiet = quiet();
    let prepared = prepare_observed(inputs.clone(), &asks, &mut quiet).unwrap();
    let normal = evaluate_observed(prepared, &mut quiet).unwrap();
    assert_eq!(normal.status(), "partial", "{:?}", normal.issues);
    assert_eq!(normal.answers[1].status, Decision::Refuted);
    assert_eq!(normal.answers[2].status, Decision::Undetermined);
    assert_eq!(normal.answers[3].status, Decision::Established);
    assert!(
        normal.answers[2]
            .reasons
            .iter()
            .flat_map(|r| &r.missing)
            .any(|f| f.subject == "q" && f.field.as_deref() == Some("Reservations.State.free"))
    );
    let expected = crate::result::Signal::Term;
    let armed = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let seen = Rc::new(Cell::new(false));
    let (arm, count, freeze) = (armed.clone(), probes.clone(), frozen.clone());
    let mut control = Control::new(move |checkpoint| {
        count.set(count.get() + 1);
        if arm.replace(false) {
            assert_eq!(checkpoint, Checkpoint::FiniteIteration);
            assert!(freeze.replace(Some(count.get())).is_none());
            Some(crate::result::Signal::Term)
        } else {
            None
        }
    });
    let prepared = prepare_observed(inputs, &asks, &mut control).unwrap();
    let stopped = evaluate_observed_with_validator(
        prepared,
        &mut control,
        |environment, graph, request, answer| {
            environment.validate_answer(graph, request, answer)?;
            if request.id == "hole" {
                let (arm, observed) = (armed.clone(), seen.clone());
                data::observe_iterations(move |_span, context, operation, index| {
                    if context.request == 3
                        && context.case.is_none()
                        && operation == "owned_family_enum"
                        && index == 0
                    {
                        assert!(!observed.replace(true));
                        arm.set(true);
                    }
                });
            }
            Ok(())
        },
    );
    data::clear_iteration_observer();
    let stopped = stopped.unwrap();
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted", "{:?}", stopped.issues);
    assert_eq!(control.stop_reason(), Some(expected));
    let Json::Obj(ref normal_wire) = normal.wire() else {
        unreachable!()
    };
    let Json::Obj(ref stopped_wire) = stopped.wire() else {
        unreachable!()
    };
    let Json::Arr(normal_nodes) = &normal_wire["nodes"] else {
        unreachable!()
    };
    let Json::Arr(stopped_nodes) = &stopped_wire["nodes"] else {
        unreachable!()
    };
    assert_eq!(
        stopped_nodes.as_slice(),
        &normal_nodes[..stopped.nodes.len()]
    );
    assert_eq!(
        stopped.contexts.as_slice(),
        &normal.contexts[..stopped.nodes.len()]
    );
    assert_eq!(
        format!("{:?}", &stopped.frames),
        format!("{:?}", &normal.frames[..stopped.frames.len()])
    );
    assert_eq!(
        format!("{:?}", &stopped.iterations),
        format!("{:?}", &normal.iterations[..stopped.iterations.len()])
    );
    assert_eq!(
        format!("{:?}", &stopped.instances),
        format!("{:?}", &normal.instances[..stopped.instances.len()])
    );
    assert_eq!(
        format!("{:?}", &stopped.cases),
        format!("{:?}", &normal.cases[..stopped.cases.len()])
    );
    assert_eq!(
        format!("{:?}", &stopped.universal_witnesses),
        format!(
            "{:?}",
            &normal.universal_witnesses[..stopped.universal_witnesses.len()]
        )
    );
    let Json::Arr(normal_answers) = &normal_wire["answers"] else {
        unreachable!()
    };
    let Json::Arr(stopped_answers) = &stopped_wire["answers"] else {
        unreachable!()
    };
    assert_eq!(&stopped_answers[..3], &normal_answers[..3]);
    for answer in &stopped.answers[3..] {
        assert_eq!(answer.status, Decision::Undetermined);
        assert!(answer.outputs.is_empty() && answer.claim.is_none() && answer.evidence.is_empty());
        let reason = answer
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(actual) if actual==&expected))
            .unwrap();
        let Json::Obj(ref wire) = reason.wire() else {
            unreachable!()
        };
        let Json::Obj(ref expected_wire) = expected.issue() else {
            unreachable!()
        };
        assert_eq!(wire["details"], expected_wire["details"]);
    }
    assert!(
        !stopped
            .nodes
            .iter()
            .enumerate()
            .any(|(i, n)| stopped.contexts[i].request == 3
                && matches!(n.payload, Some(Payload::FiniteExhaustion { .. })))
    );
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}
