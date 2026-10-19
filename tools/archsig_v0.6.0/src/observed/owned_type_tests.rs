fn owned_type_private_completed_missing(result: &ObservedEvaluation, law: &str, original: &str) {
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    let answer = &result.answers[0];
    let expected = original.starts_with("forall");
    assert_eq!(
        data_scalar_at(result, answer.outputs["value"].0),
        &Scalar::Bool(expected)
    );
    assert!(answer.scope.completions);
    assert!(
        answer
            .reasons
            .iter()
            .flat_map(|r| &r.missing)
            .any(|f| f.snapshot == "v"
                && f.subject == "item"
                && f.field.as_deref() == Some("Roster.E.owner"))
    );
    assert!(
        !answer
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }))
    );
    let domains: Vec<_> = result
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| {
            let Some(Payload::Domain { elements, .. }) = &n.payload else {
                return None;
            };
            let source = n.arguments.first()?;
            let Some(Payload::Expression {
                location: Location::Law { span },
                ..
            }) = &result.nodes[source.0].payload
            else {
                return None;
            };
            (result.contexts[i].case.is_some() && law.get(span.0..span.1) == Some(original))
                .then_some(elements)
        })
        .collect();
    assert_eq!(domains.len(), 2, "v/wの登録rootによる全補完");
    let values: Vec<_> = domains[0]
        .iter()
        .map(|r| data_scalar_at(result, r.0).clone())
        .collect();
    let item = Scalar::Subject {
        snapshot: "v".into(),
        subject: "item".into(),
        entity: "Roster.E".into(),
    };
    let wanted = if expected {
        vec![item]
    } else {
        let ref_ty = Type::Ref("Roster.E".into());
        let set_ty = Type::Set(Box::new(ref_ty.clone()));
        vec![
            Scalar::Tuple(vec![
                Scalar::Unit,
                Scalar::Option {
                    element: set_ty.clone(),
                    value: None,
                },
            ]),
            Scalar::Tuple(vec![
                Scalar::Unit,
                Scalar::Option {
                    element: set_ty.clone(),
                    value: Some(Box::new(Scalar::Set {
                        element: ref_ty.clone(),
                        items: vec![],
                    })),
                },
            ]),
            Scalar::Tuple(vec![
                Scalar::Unit,
                Scalar::Option {
                    element: set_ty,
                    value: Some(Box::new(Scalar::Set {
                        element: ref_ty,
                        items: vec![item],
                    })),
                },
            ]),
        ]
    };
    assert_eq!(values, wanted);
    let other: Vec<_> = domains[1]
        .iter()
        .map(|r| data_scalar_at(result, r.0).clone())
        .collect();
    let empty_fiber = if expected {
        vec![]
    } else {
        wanted[..2].to_vec()
    };
    assert_eq!(other, empty_fiber, "異なるsnapshotのownerは空fiber");
    rebuild_for_origin_and_support_recheck(result, &result.nodes).unwrap();
}

const OWNED_TYPE_VIEW: &str = "view every(a:System):Bool=forall s:State[a] . true;";

fn owned_type_private_domains(result: &ObservedEvaluation, request: usize) -> Vec<usize> {
    result
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, node)| {
            if result.contexts[i].request != request || result.contexts[i].case.is_some() {
                return None;
            }
            let Some(Payload::Domain { .. }) = &node.payload else {
                return None;
            };
            let source = *node.arguments.first()?;
            let Some(Payload::Expression {
                location: Location::Law { span },
                ..
            }) = &result.nodes[source.0].payload
            else {
                return None;
            };
            result
                .prepared
                .inputs()
                .law()
                .exprs
                .iter()
                .any(|e| {
                    e.span == *span
                        && matches!(
                            e.kind,
                            ExprKind::Quant {
                                split: crate::law::ast::QuantSplit::Fixed {
                                    domain: crate::law::ast::QuantDomain::Type(_),
                                    ..
                                },
                                ..
                            }
                        )
                })
                .then_some(i)
        })
        .collect()
}

fn owned_type_private_elements(result: &ObservedEvaluation, domain: usize) -> Vec<NodeRef> {
    let Some(Payload::Domain { ty, elements }) = &result.nodes[domain].payload else {
        panic!("Domain")
    };
    assert!(
        elements
            .iter()
            .all(|r| result.nodes[r.0].ty == NodeType::Value(ty.clone()))
    );
    elements.clone()
}

#[test]
fn owned_type_quantification_rechecks_original_source_owner_domain_and_member_prefixes() {
    let result = owned_private_example(
        OWNED_TYPE_VIEW,
        &[
            "first=evaluate(Reservations.every,a=@v/A)",
            "other=evaluate(Reservations.every,a=@v/B)",
            "snapshot=evaluate(Reservations.every,a=@w/A)",
            "again=evaluate(Reservations.every,a=@v/A)",
            "empty=evaluate(Reservations.every,a=@v/Z)",
        ],
        None,
        false,
    );
    assert_eq!(result.status(), "complete");
    let domain = owned_type_private_domains(&result, 3)[0];
    let prior = owned_type_private_domains(&result, 0)[0];
    let elements = owned_type_private_elements(&result, domain);
    assert_eq!(elements.len(), 2);
    let source = result.nodes[domain].arguments[0].0;
    let owner = result.nodes[domain].arguments[1];
    let prior_owner = result.nodes[prior].arguments[1];
    assert_ne!(owner, prior_owner);
    assert_eq!(
        data_scalar_at(&result, owner.0),
        data_scalar_at(&result, prior_owner.0)
    );
    assert_eq!(result.nodes[source].arguments.last(), Some(&owner));
    assert_eq!(result.nodes[domain].arguments[2..], elements);
    assert_eq!(
        reservations_private_text(&result, NodeRef(source)),
        "forall s:State[a] . true"
    );
    for element in &elements {
        assert_eq!(
            result.nodes[element.0].arguments,
            vec![NodeRef(source), owner]
        );
        assert_eq!(
            result.nodes[element.0].support,
            result.nodes[domain].support
        );
        assert!(
            matches!(data_scalar_at(&result, element.0), Scalar::Subject {snapshot,subject,entity} if snapshot=="v" && ["p","q"].contains(&subject.as_str()) && entity=="Reservations.State")
        );
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=element.0]).unwrap();
    }
    assert!(
        result.nodes[domain]
            .support
            .iter()
            .any(|f| f.field.as_deref() == Some("Reservations.State.owner"))
    );
    let empty = owned_type_private_domains(&result, 4)[0];
    assert!(owned_type_private_elements(&result, empty).is_empty());
    assert!(!result.nodes[empty].support.is_empty());
    for variant in 0..6 {
        completion_mutation(&result, source, |nodes| match variant {
            0 => {
                nodes[source].arguments.pop();
            }
            1 => {
                *nodes[source].arguments.last_mut().unwrap() = prior_owner;
            }
            2 => {
                nodes[source].scope.completions = true;
            }
            3 => {
                nodes[source].scope.readings.insert("Foreign".into());
            }
            4 => {
                let Some(Payload::Expression {
                    location: Location::Law { span },
                    ..
                }) = &mut nodes[source].payload
                else {
                    unreachable!()
                };
                span.0 += 1;
            }
            _ => {
                nodes[source].ty = NodeType::Expression(Type::Unit);
            }
        });
    }
    completion_mutation(&result, elements[0].0, |nodes| {
        nodes[elements[0].0].arguments[1] = prior_owner;
    });
    completion_mutation(&result, elements[0].0, |nodes| {
        nodes[elements[0].0].support.clear();
    });
    for variant in 0..5 {
        completion_mutation(&result, domain, |nodes| match variant {
            0 => {
                let Some(Payload::Domain { elements, .. }) = &mut nodes[domain].payload else {
                    unreachable!()
                };
                elements.pop();
                nodes[domain].arguments.pop();
            }
            1 => {
                let Some(Payload::Domain { elements, .. }) = &mut nodes[domain].payload else {
                    unreachable!()
                };
                let extra = elements[0];
                elements.push(extra);
                nodes[domain].arguments.push(extra);
            }
            2 => {
                let Some(Payload::Domain { elements, .. }) = &mut nodes[domain].payload else {
                    unreachable!()
                };
                let duplicate = elements[0];
                elements[1] = duplicate;
                nodes[domain].arguments[3] = duplicate;
            }
            3 => {
                nodes[domain].arguments[1] = prior_owner;
            }
            _ => {
                nodes[domain].scope.quantifiers[0].name = "foreign".into();
            }
        });
    }
}

#[test]
fn owned_type_quantification_tuple_option_set_members_keep_each_original_owner() {
    let result = owned_private_example(
        "view pairs(a:System,b:System):Bool=forall x:(State[a],State[b]) . true; view options(a:System):Bool=forall x:Option<State[a]> . true; view powers(a:System):Bool=forall x:Set<State[a]> . true;",
        &[
            "pairs=evaluate(Reservations.pairs,a=@v/A,b=@v/B)",
            "options=evaluate(Reservations.options,a=@v/A)",
            "powers=evaluate(Reservations.powers,a=@v/A)",
        ],
        None,
        false,
    );
    assert_eq!(result.status(), "complete");
    let domains: Vec<_> = (0..3)
        .map(|r| owned_type_private_domains(&result, r)[0])
        .collect();
    assert_eq!(owned_type_private_elements(&result, domains[0]).len(), 4);
    assert_eq!(owned_type_private_elements(&result, domains[1]).len(), 3);
    assert_eq!(owned_type_private_elements(&result, domains[2]).len(), 4);
    let tuple = owned_type_private_elements(&result, domains[0])[0].0;
    let option = owned_type_private_elements(&result, domains[1])
        .into_iter()
        .find(|r| {
            matches!(
                data_scalar_at(&result, r.0),
                Scalar::Option { value: Some(_), .. }
            )
        })
        .unwrap()
        .0;
    let set = owned_type_private_elements(&result, domains[2])
        .into_iter()
        .find(|r| matches!(data_scalar_at(&result,r.0),Scalar::Set{items,..} if items.len()==2))
        .unwrap()
        .0;
    let source = result.nodes[domains[0]].arguments[0].0;
    assert_eq!(
        result.nodes[domains[0]].arguments[1..3],
        result.nodes[source].arguments[result.nodes[source].arguments.len() - 2..]
    );
    completion_mutation(&result, source, |nodes| {
        let len = nodes[source].arguments.len();
        nodes[source].arguments.swap(len - 1, len - 2);
    });
    completion_mutation(&result, tuple, |nodes| {
        let Some(Payload::Scalar(Scalar::Tuple(items))) = &mut nodes[tuple].payload else {
            unreachable!()
        };
        assert_ne!(items[0], items[1]);
        items.swap(0, 1);
    });
    completion_mutation(&result, option, |nodes| {
        let Some(Payload::Scalar(Scalar::Option { value, .. })) = &mut nodes[option].payload else {
            unreachable!()
        };
        let Some(item) = value else { unreachable!() };
        let Scalar::Subject { subject, .. } = item.as_mut() else {
            unreachable!()
        };
        *subject = "r".into();
    });
    completion_mutation(&result, set, |nodes| {
        let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut nodes[set].payload else {
            unreachable!()
        };
        let Scalar::Subject { subject, .. } = &mut items[0] else {
            unreachable!()
        };
        *subject = "r".into();
    });
    let mut reordered = result.nodes[..=set].to_vec();
    let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut reordered[set].payload else {
        unreachable!()
    };
    items.reverse();
    assert_ne!(
        format!("{reordered:?}"),
        format!("{:?}", &result.nodes[..=set])
    );
    rebuild_for_origin_and_support_recheck(&result, &reordered).unwrap();
    completion_mutation(&result, set, |nodes| {
        let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut nodes[set].payload else {
            unreachable!()
        };
        let Scalar::Subject { snapshot, .. } = &mut items[0] else {
            unreachable!()
        };
        *snapshot = "w".into();
    });
}

#[test]
fn owned_type_quantification_let_and_if_sources_wait_for_real_rhs_order() {
    let result = owned_private_example(
        "view staged(m:Migration):Bool=if true then (let a=m.to in forall s:State[a] . true) else (let b=m.from in forall t:State[b] . true);",
        &["current=evaluate(Reservations.staged,m=@v/m)"],
        None,
        false,
    );
    assert_eq!(result.status(), "complete");
    let domains = owned_type_private_domains(&result, 0);
    assert_eq!(domains.len(), 2);
    let left = result.nodes[domains[0]].arguments[0].0;
    let right = result.nodes[domains[1]].arguments[0].0;
    let lhs = result.nodes[domains[0]].arguments[1].0;
    let rhs = result.nodes[domains[1]].arguments[1].0;
    assert!(lhs < left && left < rhs && rhs < right);
    assert_eq!(
        reservations_private_text(
            &result,
            match &result.nodes[lhs].payload {
                Some(Payload::Evaluation { expression, .. }) => *expression,
                _ => panic!("actual let RHS"),
            }
        ),
        "m.to"
    );
    assert_eq!(
        reservations_private_text(
            &result,
            match &result.nodes[rhs].payload {
                Some(Payload::Evaluation { expression, .. }) => *expression,
                _ => panic!("actual let RHS"),
            }
        ),
        "m.from"
    );
    completion_mutation(&result, right, |nodes| {
        *nodes[right].arguments.last_mut().unwrap() = NodeRef(lhs);
    });
}

#[test]
fn owned_type_quantification_unknown_owner_keeps_type_location_missing_and_completions() {
    let result = owned_private_example(
        "view uncertain(m:Migration):Bool=let a=m.from in forall s:State[a] . true;",
        &["current=evaluate(Reservations.uncertain,m=@v/m)"],
        Some("m-from"),
        false,
    );
    assert_eq!(result.status(), "complete");
    assert!(result.answers[0].scope.completions);
    assert_eq!(
        data_scalar_at(&result, result.answers[0].outputs["value"].0),
        &Scalar::Bool(true)
    );
    assert!(
        !result.answers[0]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }))
    );
    assert!(owned_type_private_domains(&result, 0).is_empty());
    let evaluation = reservations_private_evaluations(&result, "forall s:State[a] . true")[0];
    let Some(Payload::Evaluation {
        expression,
        value,
        parts,
        ..
    }) = &result.nodes[evaluation].payload
    else {
        unreachable!()
    };
    assert!(value.is_none() && parts[0].children.is_empty());
    let owner = *result.nodes[expression.0].arguments.last().unwrap();
    assert!(owner.0 < expression.0);
    assert!(matches!(
        result.nodes[owner.0].payload,
        Some(Payload::Evaluation { value: None, .. })
    ));
    let reason = result.nodes[evaluation]
        .reasons
        .iter()
        .find(|r| matches!(r.kind, ReasonKind::Missing))
        .unwrap();
    let Some(Location::Law { span }) = reason.location else {
        unreachable!()
    };
    assert_eq!(
        &result.prepared.inputs().sources().law().bytes()[span.0..span.1],
        b"State[a]"
    );
    assert_eq!(reason.dependencies, vec![*expression]);
    assert!(
        result.answers[0]
            .reasons
            .iter()
            .flat_map(|r| &r.missing)
            .any(|f| f.subject == "m" && f.field.as_deref() == Some("Reservations.Migration.from"))
    );
    completion_mutation(&result, expression.0, |nodes| {
        nodes[expression.0].arguments.pop();
    });
    completion_mutation(&result, evaluation, |nodes| {
        nodes[evaluation].scope.completions = false;
    });
    completion_mutation(&result, evaluation, |nodes| {
        nodes[evaluation]
            .reasons
            .retain(|r| !matches!(r.kind, ReasonKind::Missing));
    });
    completion_mutation(&result, evaluation, |nodes| {
        let reason = nodes[evaluation]
            .reasons
            .iter_mut()
            .find(|r| matches!(r.kind, ReasonKind::Missing))
            .unwrap();
        reason.location = Some(Location::Law {
            span: (span.0 + 1, span.1),
        });
    });
    completion_mutation(&result, evaluation, |nodes| {
        let missing = nodes[evaluation]
            .reasons
            .iter_mut()
            .find(|r| matches!(r.kind, ReasonKind::Missing))
            .unwrap();
        assert_eq!(missing.missing[0].subject, "m");
        missing.missing[0].subject = "e".into();
    });
}

#[test]
fn owned_type_quantification_missing_body_counterexample_and_checked_are_rechecked() {
    let result = owned_private_example(
        "law required trial(a:System):forall s:State[a] . s.free>0;",
        &["current=check(Reservations.trial,a=@v/A)"],
        Some("q-free"),
        true,
    );
    assert_eq!(result.status(), "complete");
    assert_eq!(result.answers[0].status, Decision::Refuted);
    let domain = owned_type_private_domains(&result, 0)[0];
    assert_eq!(owned_type_private_elements(&result, domain).len(), 2);
    assert!(
        result.answers[0]
            .reasons
            .iter()
            .flat_map(|r| &r.missing)
            .any(|f| f.subject == "q")
    );
    let counter = result
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (result.contexts[i].case.is_none()
                && matches!(n.payload, Some(Payload::Counterexample { .. })))
            .then_some(i)
        })
        .unwrap();
    completion_mutation(&result, counter, |nodes| {
        let Some(Payload::Counterexample { bindings, .. }) = &mut nodes[counter].payload else {
            unreachable!()
        };
        bindings[0].name = "foreign".into();
    });
    let full = owned_private_example(
        OWNED_TYPE_VIEW,
        &["current=evaluate(Reservations.every,a=@v/A)"],
        None,
        false,
    );
    let exhaustion = full
        .nodes
        .iter()
        .position(|n| matches!(n.payload, Some(Payload::FiniteExhaustion { .. })))
        .unwrap();
    completion_mutation(&full, exhaustion, |nodes| {
        let Some(Payload::FiniteExhaustion { checked, .. }) = &mut nodes[exhaustion].payload else {
            unreachable!()
        };
        assert_eq!(*checked, 2);
        *checked = 1;
    });
}

#[test]
fn owned_type_quantification_call_pattern_and_outer_iteration_keep_actual_producers() {
    let mut result = owned_private_example(
        "view inside(a:System):Bool=forall s:State[a] . true; view called(m:Migration):Bool=inside(m.from) and inside(m.from); view patterned(a:System):Bool=match a { held=>forall s:State[held] . true; }; view outside():Bool=forall a:System . forall s:State[a] . true;",
        &[
            "calls=evaluate(Reservations.called,m=@v/m)",
            "pattern=evaluate(Reservations.patterned,a=@v/A)",
            "outer=evaluate(Reservations.outside)",
        ],
        None,
        false,
    );
    assert_eq!(result.status(), "complete");
    let calls = owned_type_private_domains(&result, 0);
    assert_eq!(calls.len(), 2);
    let first = result.nodes[calls[0]].arguments[1];
    let second = result.nodes[calls[1]].arguments[1];
    assert_ne!(first, second);
    let Some(Payload::Evaluation {
        value: first_value, ..
    }) = &result.nodes[first.0].payload
    else {
        panic!("first actual call argument")
    };
    let Some(Payload::Evaluation {
        value: second_value,
        ..
    }) = &result.nodes[second.0].payload
    else {
        panic!("second actual call argument")
    };
    assert_eq!(
        data_scalar_at(&result, first_value.unwrap().0),
        data_scalar_at(&result, second_value.unwrap().0)
    );
    let source = result.nodes[calls[1]].arguments[0].0;
    assert_ne!(
        result.contexts[calls[0]].frame,
        result.contexts[calls[1]].frame
    );
    completion_mutation(&result, source, |nodes| {
        *nodes[source].arguments.last_mut().unwrap() = first;
    });
    let context = result.contexts[source];
    result.contexts[source] = result.contexts[result.nodes[calls[0]].arguments[0].0];
    assert_ne!(result.contexts[source], context);
    assert!(matches!(
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=source]),
        Err(ValidationFailure::Internal(_))
    ));
    assert!(matches!(
        rebuild_for_origin_and_support_recheck(&result, &result.nodes),
        Err(ValidationFailure::Internal(_))
    ));
    result.contexts[source] = context;
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    let pattern = owned_type_private_domains(&result, 1)[0];
    let pattern_owner = result.nodes[pattern].arguments[1];
    assert!(matches!(
        result.nodes[pattern_owner.0].payload,
        Some(Payload::Evaluation { .. })
    ));
    let inner: Vec<_> = owned_type_private_domains(&result, 2)
        .into_iter()
        .filter(|d| {
            result.nodes[*d].arguments.len() > 1
                && reservations_private_text(&result, result.nodes[*d].arguments[0])
                    .starts_with("forall s:State[a]")
        })
        .collect();
    assert!(inner.len() >= 3);
    for domain in &inner {
        let owner = result.nodes[*domain].arguments[1];
        assert!(matches!(
            result.nodes[owner.0].rule,
            Rule::Construction("domain")
        ));
        assert!(result.contexts[*domain].iteration.is_some());
    }
    let later = *inner.last().unwrap();
    let later_source = result.nodes[later].arguments[0].0;
    let prior_owner = result.nodes[inner[0]].arguments[1];
    assert_ne!(result.nodes[later].arguments[1], prior_owner);
    completion_mutation(&result, later_source, |nodes| {
        *nodes[later_source].arguments.last_mut().unwrap() = prior_owner;
    });
}

fn owned_type_private_phase_stop(phase: &'static str, kind: usize) {
    use super::super::control::Usage;
    use std::{cell::Cell, rc::Rc};
    let body = "view seed():Unit=unit; law required prior():false; view hole(s:State):Z=s.free; view wrapped(a:System):Bool=forall bag:Option<Set<State[a]>> . true;";
    let current = "current=evaluate(Reservations.wrapped,a=@v/A)";
    let asks = [
        "seed=evaluate(Reservations.seed)",
        "prior=check(Reservations.prior)",
        "hole=evaluate(Reservations.hole,s=@v/q)",
        current,
        "later=evaluate(Reservations.seed)",
    ];
    let inputs = owned_private_fixture(body, Some("q-free"), false);
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
        if phase == "quant_body" {
            let domains = owned_type_private_domains(&stopped, 3);
            assert_eq!(domains.len(), 1);
            assert_eq!(owned_type_private_elements(&stopped, domains[0]).len(), 5);
            assert_eq!(stopped.iterations.len(), 1);
            let finished = stopped
                .nodes
                .iter()
                .enumerate()
                .filter(|(i, n)| {
                    stopped.contexts[*i].request == 3
                        && stopped.contexts[*i].iteration.is_some()
                        && matches!(n.payload, Some(Payload::Evaluation { .. }))
                })
                .count();
            assert_eq!(finished, 1);
        }
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}

#[test]
fn owned_type_quantification_container_cancel_preserves_completed_prefix_and_prior_answers() {
    owned_type_private_phase_stop("type_enum", 0);
}
#[test]
fn owned_type_quantification_member_memory_stop_preserves_completed_prefix() {
    owned_type_private_phase_stop("quant_domain", 2);
}
#[test]
fn owned_type_quantification_body_time_stop_keeps_finished_iteration_without_whole_evidence() {
    owned_type_private_phase_stop("quant_body", 1);
}
#[test]
fn owned_type_quantification_answer_cancel_preserves_verified_current_result() {
    owned_type_private_phase_stop("answer", 0);
}

#[test]
fn owned_type_quantification_recheck_stops_and_success_memo_are_session_local() {
    use super::super::control::Usage;
    use std::{cell::Cell, rc::Rc};
    let result = owned_private_example(
        OWNED_TYPE_VIEW,
        &["value=evaluate(Reservations.every,a=@v/A)"],
        None,
        false,
    );
    let domain = owned_type_private_domains(&result, 0)[0];
    let source = result.nodes[domain].arguments[0].0;
    let value = owned_type_private_elements(&result, domain)[0].0;
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

#[test]
fn owned_type_quantification_rejects_valid_original_type_resolution_and_index_transfers() {
    use crate::law::ast::{QuantDomain, QuantSplit, TypeAst};
    let result = owned_private_example(
        "view origins(a:System,b:System):(Bool,Bool,Bool,Bool)=((forall x:State[a] . true),(forall x:Reservations.State[a] . true),(forall x:Reserve[a] . true),(forall x:State[b] . true));",
        &["current=evaluate(Reservations.origins,a=@v/A,b=@v/B)"],
        None,
        false,
    );
    assert_eq!(result.status(), "complete");
    let domains = owned_type_private_domains(&result, 0);
    assert_eq!(domains.len(), 4);
    let law = result.prepared.inputs().law();
    let bytes = result.prepared.inputs().sources().law().bytes();
    let expected = [
        ("State[a]", "State", "Reservations.State", "a", 2),
        (
            "Reservations.State[a]",
            "Reservations.State",
            "Reservations.State",
            "a",
            2,
        ),
        ("Reserve[a]", "Reserve", "Reservations.Reserve", "a", 1),
        ("State[b]", "State", "Reservations.State", "b", 2),
    ];
    let mut sources = Vec::new();
    let mut indices = Vec::new();
    for (&domain, (original, spelling, resolved, owner_name, count)) in domains.iter().zip(expected)
    {
        let source = result.nodes[domain].arguments[0];
        let Some(Payload::Expression {
            location: Location::Law { span },
            bindings,
            ..
        }) = &result.nodes[source.0].payload
        else {
            panic!("actual quantifier Source")
        };
        let (id, expression) = law
            .exprs
            .iter()
            .enumerate()
            .find(|(id, e)| e.span == *span && law.quantifier_types[*id].is_some())
            .unwrap();
        let ExprKind::Quant {
            split:
                QuantSplit::Fixed {
                    domain:
                        QuantDomain::Type(TypeAst::Named {
                            name,
                            index: Some(index),
                            span: type_span,
                        }),
                    ..
                },
            ..
        } = &expression.kind
        else {
            panic!("original named Owned TypeAst")
        };
        assert_eq!(&bytes[type_span.0..type_span.1], original.as_bytes());
        assert_eq!(&bytes[name.span().0..name.span().1], spelling.as_bytes());
        assert_eq!(name.text(), spelling);
        assert_eq!(index.name, owner_name);
        assert_eq!(&bytes[index.span.0..index.span.1], owner_name.as_bytes());
        assert!(name.span().1 < index.span.0 && index.span.1 < type_span.1);
        let targets: Vec<_> = law
            .infos
            .iter()
            .flat_map(|info| &info.references)
            .filter(|(at, _)| *at == name.span())
            .map(|(_, target)| target.as_str())
            .collect();
        assert!(!targets.is_empty());
        assert!(targets.iter().all(|target| *target == resolved));
        let ty = Type::Ref(resolved.into());
        assert_eq!(law.quantifier_types[id].as_ref(), Some(&ty));
        let Some(Payload::Domain {
            ty: actual,
            elements,
        }) = &result.nodes[domain].payload
        else {
            unreachable!()
        };
        assert_eq!(actual, &ty);
        assert_eq!(elements.len(), count);
        let owner = bindings
            .iter()
            .find(|binding| binding.name == owner_name)
            .unwrap()
            .value;
        assert_eq!(result.nodes[source.0].arguments.last(), Some(&owner));
        assert_eq!(result.nodes[domain].arguments[1], owner);
        assert_eq!(result.contexts[source.0], result.contexts[domain]);
        assert!(
            result.contexts[source.0].frame.is_none()
                && result.contexts[source.0].iteration.is_none()
        );
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=domain]).unwrap();
        indices.push(index.span);
        sources.push(source);
    }
    assert!(indices.windows(2).all(|pair| pair[0] != pair[1]));
    assert_ne!(indices[0], indices[2]);
    // 同じRequest・Contextの実在Source全体を移す。Source単体は合法でも、
    // 元TypeAst・静的解決・添字出現が変わり、保持したDomainと不整合になる。
    for (target, donor) in [(1, 0), (2, 1), (3, 0)] {
        let source = sources[target].0;
        let replacement = result.nodes[sources[donor].0].clone();
        assert!(sources[donor].0 < source && source < domains[target]);
        assert_eq!(result.contexts[source], result.contexts[sources[donor].0]);
        assert_ne!(
            reservations_private_text(&result, sources[target]),
            reservations_private_text(&result, sources[donor])
        );
        let mut legal_source = result.nodes[..=source].to_vec();
        legal_source[source] = replacement.clone();
        assert_ne!(
            format!("{legal_source:?}"),
            format!("{:?}", &result.nodes[..=source])
        );
        rebuild_for_origin_and_support_recheck(&result, &legal_source).unwrap();
        completion_mutation(&result, domains[target], |nodes| {
            nodes[source] = replacement.clone();
        });
    }
}

#[test]
fn owned_type_quantification_option_tag_changes_are_legal_members_but_rejected_in_complete_domain()
{
    let result = owned_private_example(
        "view options(a:System):Bool=forall x:Option<State[a]> . true;",
        &["current=evaluate(Reservations.options,a=@v/A)"],
        None,
        false,
    );
    assert_eq!(result.status(), "complete");
    let domain = owned_type_private_domains(&result, 0)[0];
    let elements = owned_type_private_elements(&result, domain);
    assert_eq!(elements.len(), 3);
    let element = Type::Ref("Reservations.State".into());
    let none = elements
        .iter()
        .find(|r| {
            matches!(
                data_scalar_at(&result, r.0),
                Scalar::Option { value: None, .. }
            )
        })
        .unwrap()
        .0;
    let somes: Vec<_> = elements
        .iter()
        .filter(|r| {
            matches!(
                data_scalar_at(&result, r.0),
                Scalar::Option { value: Some(_), .. }
            )
        })
        .copied()
        .collect();
    assert_eq!(somes.len(), 2);
    assert!(
        elements
            .iter()
            .all(|r| result.nodes[r.0].ty
                == NodeType::Value(Type::Option(Box::new(element.clone()))))
    );
    for (target, donor) in [(somes[0].0, none), (none, somes[0].0)] {
        let Some(Payload::Scalar(Scalar::Option {
            element: original_element,
            value: original_tag,
        })) = &result.nodes[target].payload
        else {
            unreachable!()
        };
        let Some(Payload::Scalar(Scalar::Option {
            element: replacement_element,
            value: replacement_tag,
        })) = &result.nodes[donor].payload
        else {
            unreachable!()
        };
        assert_eq!(original_element, &element);
        assert_eq!(replacement_element, &element);
        assert_ne!(original_tag.is_some(), replacement_tag.is_some());
        assert_eq!(
            result.nodes[target].arguments,
            result.nodes[donor].arguments
        );
        assert_eq!(result.nodes[target].scope, result.nodes[donor].scope);
        assert_eq!(result.nodes[target].support, result.nodes[donor].support);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
        let replacement = result.nodes[donor].payload.clone();
        let mut legal_member = result.nodes[..=target].to_vec();
        legal_member[target].payload = replacement.clone();
        assert_ne!(
            format!("{legal_member:?}"),
            format!("{:?}", &result.nodes[..=target])
        );
        // 将来nodeのRefを使わず、このmemberの生のOption tag/valueだけを変える。
        rebuild_for_origin_and_support_recheck(&result, &legal_member).unwrap();
        completion_mutation(&result, domain, |nodes| {
            nodes[target].payload = replacement.clone();
        });
    }
}

#[test]
fn owned_type_quantification_rejects_empty_and_short_actual_call_frame_arguments() {
    let mut result = owned_private_example(
        "view inner(a:System,b:System):Bool=forall s:State[b] . true; view caller(m:Migration):Bool=inner(m.from,m.to);",
        &["current=evaluate(Reservations.caller,m=@v/m)"],
        None,
        false,
    );
    assert_eq!(result.status(), "complete");
    let domains = owned_type_private_domains(&result, 0);
    assert_eq!(domains.len(), 1);
    let source = result.nodes[domains[0]].arguments[0].0;
    assert_eq!(
        reservations_private_text(&result, NodeRef(source)),
        "forall s:State[b] . true"
    );
    let frame = result.contexts[source].frame.expect("actual callee frame");
    let original = result.frames[frame].arguments.clone();
    assert_eq!(original.len(), 2);
    assert!(original.iter().all(|argument| argument.0 < source
        && matches!(
            result.nodes[argument.0].payload,
            Some(Payload::Evaluation { .. })
        )));
    assert_eq!(result.nodes[source].arguments.last(), Some(&original[1]));
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=source]).unwrap();
    let normal_nodes = format!("{:?}", result.nodes);
    let normal_contexts = result.contexts.clone();
    for retained in [0, 1] {
        result.frames[frame].arguments.truncate(retained);
        assert_ne!(result.frames[frame].arguments, original);
        assert_eq!(result.frames[frame].arguments.len(), retained);
        assert_eq!(format!("{:?}", result.nodes), normal_nodes);
        assert_eq!(result.contexts, normal_contexts);
        assert!(matches!(
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=source]),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            rebuild_for_origin_and_support_recheck(&result, &result.nodes),
            Err(ValidationFailure::Internal(_))
        ));
        result.frames[frame].arguments = original.clone();
    }
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=source]).unwrap();
}
