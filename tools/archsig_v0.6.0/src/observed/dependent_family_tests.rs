fn dependent_private_fixture(body: &str, flags: [Option<bool>; 2], unknown: bool) -> InputSources {
    let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Dep","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Dep.Root","meaning":"根。","parameters":[],"fields":[],"alignments":[]},{"kind":"entity","name":"Dep.Child","meaning":"根に属する対象。","parameters":[{"name":"owner","type":["Ref","Dep.Root"],"meaning":"所属。"}],"fields":[],"alignments":[]},{"kind":"entity","name":"Dep.Leaf","meaning":"同じ根に属する別の対象。","parameters":[{"name":"owner","type":["Ref","Dep.Root"],"meaning":"所属。"}],"fields":[{"name":"ok","type":"Bool","meaning":"観測条件。"}],"alignments":[]}]}]}"#;
    let checked =
        crate::definition::check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Dep"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Inspect {{ use vocabulary Dep version \"1\" digest \"{digest}\"; {body} }}"
    );
    let subjects = [
        ("A", "Root"),
        ("B", "Root"),
        ("Z", "Root"),
        ("p", "Child"),
        ("q", "Child"),
        ("l", "Leaf"),
        ("m", "Leaf"),
    ]
    .map(|(id, ty)| format!(r#"{{"id":"{id}","type":"Dep.{ty}","origin":"scan"}}"#))
    .join(",");
    let mut atoms = Vec::new();
    for (id, ty, owner) in [
        ("p", "Child", "A"),
        ("q", "Child", "B"),
        ("l", "Leaf", "A"),
        ("m", "Leaf", "B"),
    ] {
        if unknown && id == "p" {
            continue;
        }
        atoms.push(format!(r#"{{"id":"{id}-owner","subject":"{id}","field":"Dep.{ty}.owner","value":["v","{owner}"],"origin":"scan"}}"#));
    }
    for (id, flag) in ["l", "m"].into_iter().zip(flags) {
        if let Some(flag) = flag {
            atoms.push(format!(r#"{{"id":"{id}-ok","subject":"{id}","field":"Dep.Leaf.ok","value":{flag},"origin":"scan"}}"#));
        }
    }
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Dep","version":"1","digest":"{digest}"}}],"sources":[{{"id":"source","uri":"urn:fixture:dependent-private","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],"origins":[{{"id":"scan","mode":"observed","method":"有限な対象と所属の観測。","locations":[{{"source":"source","path":"dependent.model","span":[0,1]}}]}}],"snapshots":[{{"id":"v","origin":"scan","subjects":[{subjects}],"atoms":[{}]}}]}}"#,
        atoms.join(",")
    );
    InputSources::from_bytes(
        vec![definitions.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
const DEPENDENT_BODY: &str = "law required chain(a:Root,b:Child[a],c:Leaf[a]) when true:c.ok;";
fn dependent_private_example(
    body: &str,
    asks: &[&str],
    flags: [Option<bool>; 2],
) -> ObservedEvaluation {
    let result = evaluate_observed_bytes(
        dependent_private_fixture(body, flags, false),
        asks,
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_ne!(result.status(), "error", "{:?}", result.issues);
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    result
}
fn dependent_private_domain(
    result: &ObservedEvaluation,
    request: usize,
) -> (usize, usize, Vec<usize>, Vec<NodeRef>) {
    let evaluation = result.answers[request].outputs["evaluation"].0;
    let domain = result.nodes[evaluation].arguments[1].0;
    let Some(Payload::Domain { elements, .. }) = &result.nodes[domain].payload else {
        panic!("dependent total Domain")
    };
    let source = result.nodes[domain].arguments[0].0;
    let domains = result.nodes[domain].arguments
        [1..result.nodes[domain].arguments.len() - elements.len()]
        .iter()
        .map(|r| r.0)
        .collect();
    (source, domain, domains, elements.clone())
}

#[test]
fn dependent_family_prefix_domains_recheck_original_types_members_order_and_support() {
    let result = dependent_private_example(
        DEPENDENT_BODY,
        &["all=check(Inspect.chain)"],
        [Some(true), Some(true)],
    );
    assert_eq!(result.status(), "complete");
    assert_eq!(result.answers[0].status, Decision::Established);
    let (source, total, domains, rows) = dependent_private_domain(&result, 0);
    assert_eq!(domains.len(), 6);
    assert_eq!(rows.len(), 2);
    for &domain in &domains {
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=domain]).unwrap();
    }
    let domain=*domains.iter().find(|&&d|matches!(&result.nodes[d].payload,Some(Payload::Domain {ty:Type::Ref(name),elements}) if name=="Dep.Child"&&!elements.is_empty())).unwrap();
    let Some(Payload::Domain { elements, .. }) = &result.nodes[domain].payload else {
        unreachable!()
    };
    let selected = elements[0];
    assert_eq!(result.nodes[domain].arguments[0], NodeRef(source));
    assert_eq!(result.nodes[domain].arguments.len(), 4);
    assert_eq!(
        result.nodes[selected.0].arguments,
        result.nodes[domain].arguments[..3]
    );
    assert!(
        result.nodes[domain]
            .support
            .iter()
            .any(|f| f.field.as_deref() == Some("Dep.Child.owner") && f.atom.is_some())
    );
    completion_mutation(&result, domain, |nodes| {
        let Some(Payload::Domain { elements, .. }) = &mut nodes[domain].payload else {
            unreachable!()
        };
        elements.clear();
        nodes[domain].arguments.pop();
    });
    completion_mutation(&result, domain, |nodes| {
        let Some(Payload::Domain { elements, .. }) = &mut nodes[domain].payload else {
            unreachable!()
        };
        elements.push(selected);
        nodes[domain].arguments.push(selected);
    });
    completion_mutation(&result, domain, |nodes| {
        let Some(Payload::Domain { ty, .. }) = &mut nodes[domain].payload else {
            unreachable!()
        };
        *ty = Type::Ref("Dep.Root".into());
    });
    completion_mutation(&result, domain, |nodes| {
        nodes[domain].support.pop();
    });
    completion_mutation(&result, domain, |nodes| {
        nodes[domain].scope.modes.clear();
    });
    let root_domain = domains[0];
    let Some(Payload::Domain {
        elements: roots, ..
    }) = &result.nodes[root_domain].payload
    else {
        unreachable!()
    };
    assert_eq!(roots.len(), 3);
    completion_mutation(&result, domain, |nodes| {
        nodes[domain].arguments[2] = roots[1];
    });
    completion_mutation(&result, root_domain, |nodes| {
        let Some(Payload::Domain { elements, .. }) = &mut nodes[root_domain].payload else {
            unreachable!()
        };
        elements.swap(0, 1);
        nodes[root_domain].arguments.swap(1, 2);
    });
    completion_mutation(&result, total, |nodes| {
        let Some(Payload::Domain { elements, .. }) = &mut nodes[total].payload else {
            unreachable!()
        };
        elements.pop();
        nodes[total].arguments.pop();
    });
    completion_mutation(&result, total, |nodes| {
        nodes[total].arguments.swap(1, 2);
    });
}

#[test]
fn dependent_family_rows_recheck_owner_tuple_context_and_actual_parameter_producers() {
    let result = dependent_private_example(
        DEPENDENT_BODY,
        &["first=check(Inspect.chain)", "again=check(Inspect.chain)"],
        [Some(true), Some(true)],
    );
    let (_, _, _, first) = dependent_private_domain(&result, 0);
    let (source, total, _, rows) = dependent_private_domain(&result, 1);
    let row = rows[0].0;
    let Scalar::Tuple(items) = data_scalar_at(&result, row) else {
        panic!("dependent row")
    };
    assert_eq!(items.len(), 3);
    assert!(matches!(&items[0],Scalar::Subject {subject,..} if subject=="A"));
    assert!(matches!(&items[1],Scalar::Subject {subject,..} if subject=="p"));
    assert!(matches!(&items[2],Scalar::Subject {subject,..} if subject=="l"));
    completion_mutation(&result, row, |nodes| {
        let Some(Payload::Scalar(Scalar::Tuple(items))) = &mut nodes[row].payload else {
            unreachable!()
        };
        items.swap(0, 1);
    });
    completion_mutation(&result, row, |nodes| {
        nodes[row].arguments[0] = result.nodes[first[0].0].arguments[0];
    });
    completion_mutation(&result, row, |nodes| {
        nodes[row].scope.quantifiers[0].domain = None;
    });
    let parameter = result
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (result.contexts[i].request == 1
                && result.contexts[i].instance.is_some()
                && n.arguments == [NodeRef(source), NodeRef(total), rows[0]]
                && matches!(n.ty, NodeType::Value(Type::Ref(_))))
            .then_some(i)
        })
        .unwrap();
    completion_mutation(&result, parameter, |nodes| {
        nodes[parameter].arguments[2] = first[0];
    });
    completion_mutation(&result, parameter, |nodes| {
        nodes[parameter].support.clear();
    });
    let proposition = result.answers[1].claim.unwrap().0;
    completion_mutation(&result, proposition, |nodes| {
        nodes[proposition].judgment.as_mut().unwrap().status = Decision::Refuted;
    });
    let proof = result.answers[1]
        .evidence
        .iter()
        .find(|r| {
            matches!(
                result.nodes[r.0].payload,
                Some(Payload::FiniteExhaustion { .. })
            )
        })
        .unwrap()
        .0;
    completion_mutation(&result, proof, |nodes| {
        let Some(Payload::FiniteExhaustion { checked, .. }) = &mut nodes[proof].payload else {
            unreachable!()
        };
        *checked += 1;
    });
}

#[test]
fn dependent_family_fixed_selectors_and_finite_mix_recheck_original_bindings() {
    let result = dependent_private_example(
        "law required chain(a:Root,b:Child[a],c:Leaf[a],flag:Bool) when true:c.ok or flag;",
        &[
            "fixedroot=check(Inspect.chain,a=@v/A)",
            "fixedchild=check(Inspect.chain,b=@v/p)",
            "same=check(Inspect.chain,b=@v/p)",
        ],
        [Some(true), Some(true)],
    );
    assert_eq!(result.status(), "complete");
    for i in 0..3 {
        let (_, _, _, rows) = dependent_private_domain(&result, i);
        assert_eq!(rows.len(), 2);
    }
    let (source, _, domains, _) = dependent_private_domain(&result, 2);
    let (foreign, _, _, _) = dependent_private_domain(&result, 1);
    let Some(Payload::Expression {
        bindings: prior, ..
    }) = &result.nodes[foreign].payload
    else {
        unreachable!()
    };
    completion_mutation(&result, source, |nodes| {
        let Some(Payload::Expression { bindings, .. }) = &mut nodes[source].payload else {
            unreachable!()
        };
        assert_ne!(bindings[0].value, prior[0].value);
        bindings[0].value = prior[0].value;
        nodes[source].arguments[0] = prior[0].value;
    });
    let empty=domains.into_iter().find(|&d|matches!(&result.nodes[d].payload,Some(Payload::Domain {ty:Type::Ref(t),elements}) if t=="Dep.Child"&&elements.is_empty())).unwrap();
    completion_mutation(&result, empty, |nodes| {
        nodes[empty].support.clear();
    });
}

#[test]
fn dependent_family_missing_body_and_counterexample_remain_distinct_and_rechecked() {
    let result = dependent_private_example(
        DEPENDENT_BODY,
        &["all=check(Inspect.chain)"],
        [None, Some(false)],
    );
    assert_eq!(result.answers[0].status, Decision::Refuted);
    assert!(
        result.answers[0]
            .reasons
            .iter()
            .flat_map(|r| &r.missing)
            .any(|f| f.subject == "l" && f.field.as_deref() == Some("Dep.Leaf.ok"))
    );
    let counter = result
        .nodes
        .iter()
        .enumerate()
        .find_map(|(index, node)| {
            (result.contexts[index].request == 0
                && result.contexts[index].case.is_none()
                && matches!(node.payload, Some(Payload::Counterexample { .. })))
            .then_some(index)
        })
        .unwrap();
    assert!(result.contexts[counter].instance.is_some());
    completion_mutation(&result, counter, |nodes| {
        let Some(Payload::Counterexample { facts, .. }) = &mut nodes[counter].payload else {
            unreachable!()
        };
        facts.pop();
    });
    let missing = result
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (!n.reasons.is_empty()
                && matches!(n.payload, Some(Payload::Evaluation { .. }))
                && n.reasons.iter().any(|r| !r.missing.is_empty()))
            .then_some(i)
        })
        .unwrap();
    completion_mutation(&result, missing, |nodes| {
        nodes[missing].reasons[0].missing[0].subject = "m".into();
    });
}

#[test]
fn dependent_family_unknown_owner_keeps_source_missing_and_unsupported_and_rechecks_answer() {
    let result = evaluate_observed_bytes(
        dependent_private_fixture(DEPENDENT_BODY, [Some(true), Some(true)], true),
        &["all=check(Inspect.chain)"],
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "partial", "{:?}", result.issues);
    assert_eq!(result.answers[0].status, Decision::Undetermined);
    assert!(result.answers[0].scope.completions);
    assert!(
        result.answers[0].outputs.is_empty()
            && result.answers[0].claim.is_none()
            && result.answers[0].evidence.is_empty()
    );
    assert!(
        result.answers[0]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }))
    );
    assert!(
        result.answers[0]
            .reasons
            .iter()
            .flat_map(|r| &r.missing)
            .any(|f| f.snapshot == "v"
                && f.subject == "p"
                && f.field.as_deref() == Some("Dep.Child.owner"))
    );
    let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    let mut quiet = named_call_quiet();
    let environment = Environment::new(result.prepared.inputs(), &mut quiet).unwrap();
    let request = &result.prepared.requests().requests()[0];
    environment
        .validate_answer(&graph, request, &result.answers[0])
        .unwrap();
    let mut changed_scope = result.answers[0].clone();
    changed_scope.scope.completions = false;
    assert!(matches!(
        environment.validate_answer(&graph, request, &changed_scope),
        Err(ValidationFailure::Internal(_))
    ));
    let mut changed = result.answers[0].clone();
    let reason = changed
        .reasons
        .iter_mut()
        .find(|r| !r.missing.is_empty())
        .unwrap();
    reason.missing[0].subject = "q".into();
    assert!(matches!(
        environment.validate_answer(&graph, request, &changed),
        Err(ValidationFailure::Internal(_))
    ));
    let source = result
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            matches!(&n.payload,Some(Payload::Expression {parameters,..}) if !parameters.is_empty())
                .then_some(i)
        })
        .unwrap();
    assert!(!result.nodes[source].scope.completions);
    assert!(
        result
            .nodes
            .iter()
            .filter(|node| matches!(node.payload, Some(Payload::Domain { .. })))
            .all(|node| !node.scope.completions)
    );
    completion_mutation(&result, source, |nodes| {
        let Some(Payload::Expression { parameters, .. }) = &mut nodes[source].payload else {
            unreachable!()
        };
        parameters[1].1 = Type::Owned("Dep.Child".into(), "a".into());
    });
}

fn dependent_private_phase_stop(phase: &'static str, at: usize, kind: usize) {
    use super::super::control::Usage;
    use std::{cell::Cell, rc::Rc};
    let body = format!(
        "view seed():Unit=unit; law required prior():false; view hole(c:Leaf):Bool=c.ok; {DEPENDENT_BODY}"
    );
    let asks = [
        "seed=evaluate(Inspect.seed)",
        "prior=check(Inspect.prior)",
        "hole=evaluate(Inspect.hole,c=@v/l)",
        "current=check(Inspect.chain)",
        "later=evaluate(Inspect.seed)",
    ];
    let inputs = dependent_private_fixture(&body, [None, Some(false)], false);
    let mut quiet = named_call_quiet();
    let prepared = prepare_observed(inputs.clone(), &asks, &mut quiet).unwrap();
    let target = prepared.inputs().law().declarations["Inspect.chain"].span;
    let normal = evaluate_observed(prepared, &mut quiet).unwrap();
    assert_eq!(normal.status(), "partial", "{:?}", normal.issues);
    assert_eq!(normal.answers[1].status, Decision::Refuted);
    assert_eq!(normal.answers[2].status, Decision::Undetermined);
    assert_eq!(normal.answers[3].status, Decision::Refuted);
    assert!(
        normal.answers[2]
            .reasons
            .iter()
            .flat_map(|r| &r.missing)
            .any(|f| f.subject == "l" && f.field.as_deref() == Some("Dep.Leaf.ok"))
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
                data::observe_iterations(move |span, context, operation, index| {
                    if span == target
                        && context.request == 3
                        && context.case.is_none()
                        && operation == phase
                        && index == at
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
        let Json::Obj(ref reason_wire) = reason.wire() else {
            unreachable!()
        };
        let Json::Obj(ref expected_wire) = expected.wire() else {
            unreachable!()
        };
        assert_eq!(reason_wire["details"], expected_wire["details"]);
    }
    if phase != "answer" {
        let current_domains = stopped
            .nodes
            .iter()
            .enumerate()
            .filter(|(i, n)| {
                stopped.contexts[*i].request == 3
                    && matches!(n.payload, Some(Payload::Domain { .. }))
            })
            .count();
        assert!(current_domains >= 2);
        assert!(
            !stopped
                .nodes
                .iter()
                .enumerate()
                .any(|(i, n)| stopped.contexts[i].request == 3
                    && stopped.contexts[i].instance.is_none()
                    && matches!(n.payload, Some(Payload::FiniteExhaustion { .. })))
        );
        if phase == "dependent_aggregate" {
            assert!(
                stopped
                    .nodes
                    .iter()
                    .enumerate()
                    .any(|(i, n)| stopped.contexts[i].request == 3
                        && stopped.contexts[i].instance.is_some()
                        && matches!(n.payload, Some(Payload::Counterexample { .. })))
            );
        }
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn dependent_family_domain_cancel_preserves_completed_prefix_and_prior_answers() {
    dependent_private_phase_stop("dependent_domain_done", 1, 0);
}
#[test]
fn dependent_family_row_time_stop_preserves_completed_prefix_and_prior_answers() {
    dependent_private_phase_stop("dependent_row", 1, 1);
}
#[test]
fn dependent_family_aggregate_memory_stop_preserves_rows_without_whole_evidence() {
    dependent_private_phase_stop("dependent_aggregate", 0, 2);
}
#[test]
fn dependent_family_post_validation_cancel_preserves_verified_current_counterexample() {
    dependent_private_phase_stop("answer", 0, 0);
}

#[test]
fn dependent_family_recheck_stops_and_success_memo_are_session_local() {
    use super::super::control::Usage;
    use std::{cell::Cell, rc::Rc};
    let result = dependent_private_example(
        DEPENDENT_BODY,
        &["all=check(Inspect.chain)"],
        [Some(true), Some(true)],
    );
    let (source, _, domains, _) = dependent_private_domain(&result, 0);
    let target = domains[1];
    let mut graph =
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
    let mut quiet = named_call_quiet();
    let environment = Environment::new(result.prepared.inputs(), &mut quiet).unwrap();
    environment
        .recheck_node(&graph, &graph.nodes[target], target)
        .unwrap();
    let scope = graph.nodes[source].scope.clone();
    assert!(graph.nodes[source].scope.readings.insert("Foreign".into()));
    assert!(matches!(
        environment.recheck_node(&graph, &graph.nodes[target], target),
        Err(ValidationFailure::Internal(_))
    ));
    graph.nodes[source].scope = scope;
    environment
        .recheck_node(&graph, &graph.nodes[target], target)
        .unwrap();
    let before = format!(
        "{:?}",
        (
            &graph.nodes,
            &graph.contexts,
            &graph.instances,
            &graph.cases
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
            .recheck_node(&graph, &graph.nodes[target], target)
            .unwrap();
        let baseline = probes.get();
        armed.set(true);
        assert!(
            matches!(environment.recheck_node(&graph,&graph.nodes[target],target),Err(ValidationFailure::Stop(actual)) if actual==expected)
        );
        assert_eq!(probes.get(), baseline + 1);
        assert!(
            matches!(environment.recheck_node(&graph,&graph.nodes[target],target),Err(ValidationFailure::Stop(actual)) if actual==expected)
        );
        assert_eq!(control.stop_reason(), Some(expected.clone()));
        assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
        assert_eq!(probes.get(), baseline + 1);
        assert_eq!(
            format!(
                "{:?}",
                (
                    &graph.nodes,
                    &graph.contexts,
                    &graph.instances,
                    &graph.cases
                )
            ),
            before
        );
    }
}
