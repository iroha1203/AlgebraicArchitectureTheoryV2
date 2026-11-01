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

fn owned_type_private_phase_stop(phase: &'static str) {
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
        let Json::Obj(ref expected_wire) = expected.issue() else {
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
}

#[test]
fn owned_type_quantification_answer_cancel_preserves_verified_current_result() {
    owned_type_private_phase_stop("answer");
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
