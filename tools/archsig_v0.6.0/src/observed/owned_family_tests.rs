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
        &mut named_call_quiet(),
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
                .exprs
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
fn owned_expression_family_set_prefix_rechecks_type_members_support_scope_and_source() {
    let result = owned_private_example(
        OWNED_VIEW,
        &[
            "first=evaluate(Reservations.states,a=@v/A)",
            "other=evaluate(Reservations.states,a=@v/B)",
            "snapshot=evaluate(Reservations.states,a=@w/A)",
            "again=evaluate(Reservations.states,a=@v/A)",
            "empty=evaluate(Reservations.states,a=@v/Z)",
        ],
        None,
        false,
    );
    assert_eq!(result.status(), "complete");
    let evaluations = owned_private_evaluations(&result);
    assert_eq!(evaluations.len(), 5);
    let (source, Some(value), owner) = owned_private_parts(&result, evaluations[3]) else {
        panic!("known family")
    };
    let (prior_source, Some(prior_value), prior_owner) =
        owned_private_parts(&result, evaluations[0])
    else {
        panic!("known prior family")
    };
    assert_eq!(
        data_scalar_at(&result, value),
        data_scalar_at(&result, prior_value)
    );
    assert_eq!(
        result.nodes[value].arguments,
        [NodeRef(source), NodeRef(owner)]
    );
    assert!(owner < value && source < value && value < evaluations[3]);
    let Scalar::Set { element, items } = data_scalar_at(&result, value) else {
        panic!("typed family Set")
    };
    assert_eq!(element, &Type::Ref("Reservations.State".into()));
    assert_eq!(items.len(), 2);
    assert!(
        result.nodes[value]
            .support
            .iter()
            .any(|f| f.subject == "r" && f.field.as_deref() == Some("Reservations.State.owner"))
    );
    for target in [source, value, evaluations[3]] {
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
    }
    completion_mutation(&result, value, |nodes| {
        let Some(Payload::Scalar(Scalar::Set { element, .. })) = &mut nodes[value].payload else {
            unreachable!()
        };
        *element = Type::Ref("Reservations.System".into());
    });
    completion_mutation(&result, value, |nodes| {
        let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut nodes[value].payload else {
            unreachable!()
        };
        items.pop();
    });
    completion_mutation(&result, value, |nodes| {
        let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut nodes[value].payload else {
            unreachable!()
        };
        items.push(items[0].clone());
    });
    for (snapshot, subject) in [("v", "r"), ("w", "p")] {
        completion_mutation(&result, value, |nodes| {
            let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut nodes[value].payload else {
                unreachable!()
            };
            items[0] = Scalar::Subject {
                snapshot: snapshot.into(),
                subject: subject.into(),
                entity: "Reservations.State".into(),
            };
        });
    }
    completion_mutation(&result, value, |nodes| {
        nodes[value].arguments[0] = NodeRef(prior_source);
    });
    completion_mutation(&result, value, |nodes| {
        nodes[value].arguments[1] = NodeRef(prior_owner);
    });
    completion_mutation(&result, value, |nodes| {
        nodes[value].arguments.pop();
    });
    completion_mutation(&result, value, |nodes| {
        nodes[value].support.pop();
    });
    completion_mutation(&result, value, |nodes| {
        nodes[value].scope.modes.clear();
    });
    completion_mutation(&result, value, |nodes| {
        nodes[value].scope.completions = true;
    });
    completion_mutation(&result, source, |nodes| {
        nodes[source].ty = NodeType::Expression(Type::Set(Box::new(Type::Ref(
            "Reservations.Reserve".into(),
        ))));
    });
    completion_mutation(&result, evaluations[3], |nodes| {
        let Some(Payload::Evaluation { parts, .. }) = &mut nodes[evaluations[3]].payload else {
            unreachable!()
        };
        parts[0].children[0] = NodeRef(prior_owner);
        nodes[evaluations[3]].arguments[1] = NodeRef(prior_owner);
    });
    let (_, Some(empty), _) = owned_private_parts(&result, evaluations[4]) else {
        panic!("known empty family")
    };
    assert!(
        matches!(data_scalar_at(&result, empty), Scalar::Set { items, .. } if items.is_empty())
    );
    assert!(!result.nodes[empty].support.is_empty());
    completion_mutation(&result, empty, |nodes| {
        nodes[empty].support.clear();
    });
}

#[test]
fn owned_expression_family_completed_occurrences_and_call_producers_remain_exact() {
    let body = "view pair(a:System):(Set<State>,Set<State>)=(State[a],State[a]); view states(a:System):Set<State> =State[a]; view calls(a:System):(Set<State>,Set<State>)=(states(a),states(a)); view field(m:Migration):Set<State> =State[m.from]; view aliased(a:System):Set<State> =let x=a in State[x];";
    let result = owned_private_example(
        body,
        &[
            "pair=evaluate(Reservations.pair,a=@v/A)",
            "calls=evaluate(Reservations.calls,a=@v/A)",
            "field=evaluate(Reservations.field,m=@v/m)",
            "aliased=evaluate(Reservations.aliased,a=@v/A)",
        ],
        None,
        false,
    );
    assert_eq!(result.status(), "complete");
    let evaluations = owned_private_evaluations(&result);
    assert_eq!(evaluations.len(), 6);
    for (first, second) in [
        (evaluations[0], evaluations[1]),
        (evaluations[2], evaluations[3]),
    ] {
        let (first_source, Some(first_value), first_owner) = owned_private_parts(&result, first)
        else {
            panic!("first family")
        };
        let (source, Some(value), owner) = owned_private_parts(&result, second) else {
            panic!("second family")
        };
        assert_ne!(first_source, source);
        assert_ne!(first_owner, owner);
        assert_eq!(
            data_scalar_at(&result, first_value),
            data_scalar_at(&result, value)
        );
        assert!(first < value);
        completion_mutation(&result, value, |nodes| {
            nodes[value].rule = result.nodes[first_value].rule.clone();
            nodes[value].arguments = result.nodes[first_value].arguments.clone();
        });
        completion_mutation(&result, value, |nodes| {
            nodes[value].arguments[1] = NodeRef(first_owner);
        });
    }
    let (_, Some(field_value), field_owner) = owned_private_parts(&result, evaluations[4]) else {
        panic!("field owner")
    };
    assert!(
        matches!(&result.nodes[field_owner].payload,Some(Payload::Evaluation {expression,..}) if reservations_private_text(&result,*expression)=="m.from")
    );
    completion_mutation(&result, field_value, |nodes| {
        nodes[field_value].arguments[1] = NodeRef(owned_private_parts(&result, evaluations[3]).2);
    });
    let source = owned_private_parts(&result, evaluations[1]).0;
    let foreign_source = owned_private_parts(&result, evaluations[0]).0;
    completion_mutation(&result, source, |nodes| {
        let Some(Payload::Expression { location, .. }) = &mut nodes[source].payload else {
            unreachable!()
        };
        let Some(Payload::Expression {
            location: prior, ..
        }) = &result.nodes[foreign_source].payload
        else {
            unreachable!()
        };
        *location = prior.clone();
    });
}

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
        assert_eq!(result.status(), "partial");
        assert_eq!(result.answers[0].status, Decision::Undetermined);
        assert!(!result.answers[0].outputs.contains_key("value"));
        assert!(result.answers[0].scope.completions);
        assert!(result.answers[0].reasons.iter().any(|r|matches!(&r.kind,ReasonKind::UnsupportedAlgorithm {method,..} if method=="unresolved_owned_expression_family")));
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

fn owned_private_phase_stop(phase: &'static str, kind: usize) {
    use super::super::control::Usage;
    use std::{cell::Cell, rc::Rc};
    let body = format!(
        "view seed():Unit=unit; law required prior():false; view hole(s:State):Z=s.free; {OWNED_VIEW} law required walk(a:System):forall s in State[a] . s.held>=0;"
    );
    let current = if phase == "quant_body" {
        "current=check(Reservations.walk,a=@v/A)"
    } else {
        "current=evaluate(Reservations.states,a=@v/A)"
    };
    let asks = [
        "seed=evaluate(Reservations.seed)",
        "prior=check(Reservations.prior)",
        "hole=evaluate(Reservations.hole,s=@v/q)",
        current,
        "later=evaluate(Reservations.seed)",
    ];
    let inputs = owned_private_fixture(&body, Some("q-free"), false);
    let mut quiet = named_call_quiet();
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
    rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
    let (limits, usage, expected) = reservations_private_stop_usage(kind);
    let armed = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let seen = Rc::new(Cell::new(false));
    let (arm, count, freeze) = (armed.clone(), probes.clone(), frozen.clone());
    let mut control = Control::new(limits, move |checkpoint| {
        count.set(count.get() + 1);
        if arm.replace(false) {
            assert_eq!(checkpoint, Checkpoint::FiniteIteration);
            assert!(freeze.replace(Some(count.get())).is_none());
            usage
        } else {
            Usage::default()
        }
    });
    let prepared = prepare_observed(inputs, &asks, &mut control).unwrap();
    let stopped = evaluate_observed_with_validator(
        prepared,
        &mut control,
        |environment, graph, request, answer| {
            environment.validate_answer(graph, request, answer)?;
            if request.id == "hole" && phase != "answer" {
                let (arm, observed) = (armed.clone(), seen.clone());
                data::observe_iterations(move |_span, context, operation, index| {
                    if context.request == 3
                        && context.case.is_none()
                        && operation == phase
                        && index == if phase == "quant_body" { 1 } else { 0 }
                    {
                        assert!(!observed.replace(true));
                        arm.set(true);
                    }
                });
            }
            if request.id == "current" && phase == "answer" {
                assert!(!seen.replace(true));
                armed.set(true);
            }
            Ok(())
        },
    );
    data::clear_iteration_observer();
    let stopped = stopped.unwrap();
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted", "{:?}", stopped.issues);
    assert_eq!(control.stop_reason(), Some(expected.clone()));
    assert_eq!(Some(probes.get()), frozen.get());
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
    let retained = if phase == "answer" { 4 } else { 3 };
    assert_eq!(&stopped_answers[..retained], &normal_answers[..retained]);
    for answer in &stopped.answers[retained..] {
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
        let Json::Obj(ref expected_wire) = expected.wire() else {
            unreachable!()
        };
        assert_eq!(wire["details"], expected_wire["details"]);
    }
    if phase != "answer" {
        assert!(
            !stopped
                .nodes
                .iter()
                .enumerate()
                .any(|(i, n)| stopped.contexts[i].request == 3
                    && matches!(n.payload, Some(Payload::FiniteExhaustion { .. })))
        );
        if phase == "owned_family_set" || phase == "quant_body" {
            assert!(
                stopped
                    .nodes
                    .iter()
                    .enumerate()
                    .any(|(i, n)| stopped.contexts[i].request == 3
                        && matches!(n.payload, Some(Payload::Scalar(Scalar::Set { .. }))))
            );
        }
        if phase == "quant_body" {
            assert_eq!(stopped.iterations.len(), 1);
        }
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn owned_expression_family_enumeration_cancel_preserves_owner_prefix_and_prior_answers() {
    owned_private_phase_stop("owned_family_enum", 0);
}
#[test]
fn owned_expression_family_completed_set_memory_stop_preserves_scalar_prefix() {
    owned_private_phase_stop("owned_family_set", 2);
}
#[test]
fn owned_expression_family_in_iteration_time_stop_preserves_finished_body_without_exhaustion() {
    owned_private_phase_stop("quant_body", 1);
}
#[test]
fn owned_expression_family_post_validation_cancel_preserves_verified_current_set() {
    owned_private_phase_stop("answer", 0);
}

#[test]
fn owned_expression_family_recheck_stops_and_success_memo_are_session_local() {
    use super::super::control::Usage;
    use std::{cell::Cell, rc::Rc};
    let result = owned_private_example(
        OWNED_VIEW,
        &["value=evaluate(Reservations.states,a=@v/A)"],
        None,
        false,
    );
    let (source, Some(value), _) =
        owned_private_parts(&result, owned_private_evaluations(&result)[0])
    else {
        panic!("known family")
    };
    let mut graph =
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=value]).unwrap();
    let mut quiet = named_call_quiet();
    let environment = Environment::new(result.prepared.inputs(), &mut quiet).unwrap();
    environment
        .recheck_node(&graph, &graph.nodes[value], value)
        .unwrap();
    let scope = graph.nodes[source].scope.clone();
    assert!(graph.nodes[source].scope.readings.insert("Foreign".into()));
    assert!(matches!(
        environment.recheck_node(&graph, &graph.nodes[value], value),
        Err(ValidationFailure::Internal(_))
    ));
    graph.nodes[source].scope = scope;
    environment
        .recheck_node(&graph, &graph.nodes[value], value)
        .unwrap();
    let before = format!(
        "{:?}",
        (
            &graph.nodes,
            &graph.contexts,
            &graph.frames,
            &graph.iterations
        )
    );
    for kind in 0..3 {
        let (limits, usage, expected) = reservations_private_stop_usage(kind);
        let armed = Rc::new(Cell::new(false));
        let probes = Rc::new(Cell::new(0));
        let (arm, count) = (armed.clone(), probes.clone());
        let mut control = Control::new(limits, move |checkpoint| {
            count.set(count.get() + 1);
            if arm.replace(false) {
                assert_eq!(checkpoint, Checkpoint::FiniteIteration);
                usage
            } else {
                Usage::default()
            }
        });
        let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
        environment
            .recheck_node(&graph, &graph.nodes[value], value)
            .unwrap();
        let baseline = probes.get();
        armed.set(true);
        assert!(
            matches!(environment.recheck_node(&graph,&graph.nodes[value],value),Err(ValidationFailure::Stop(actual)) if actual==expected)
        );
        assert_eq!(probes.get(), baseline + 1);
        assert!(
            matches!(environment.recheck_node(&graph,&graph.nodes[value],value),Err(ValidationFailure::Stop(actual)) if actual==expected)
        );
        assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
        assert_eq!(probes.get(), baseline + 1);
        assert_eq!(
            format!(
                "{:?}",
                (
                    &graph.nodes,
                    &graph.contexts,
                    &graph.frames,
                    &graph.iterations
                )
            ),
            before
        );
    }
}
