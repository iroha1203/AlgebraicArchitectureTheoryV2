fn comprehension_flow_sources() -> InputSources {
    let definitions = include_str!("../../../../tests/fixtures/reservations.atoms.json").replace(
        r#"{"name": "free", "type": "Z""#,
        r#"{"name":"choice","type":["Option",["Ref","Reservations.State"]],"meaning":"Selected state"},
          {"name":"members","type":["List",["Ref","Reservations.State"]],"meaning":"Ordered members"},
          {"name":"enabled","type":"Bool","meaning":"Filter"},
          {"name": "free", "type": "Z""#,
    );
    let checked =
        archsig_input::definition::check_definitions(&[("flow", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies()["Reservations"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Reservations {{ use vocabulary Reservations version \"1\" digest \"{digest}\";\n\
         view selected(a:System,p:State):Set<State> = set {{ r | r in State[a] where p.choice=some(r) }};\n\
         view members(p:State):List<State> = list {{ r | r in p.members }};\n\
         view filtered(p:State):List<State> = list {{ r | r in p.members where r.enabled }};\n\
         view nested(a:System,p:State):List<State> = list {{ r | r in list {{ s | s in p.members }} where p.choice=some(r) }};\n\
         }}"
    );
    let map = include_str!("../../../../tests/fixtures/reservations.archmap.json")
        .replace("sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff", digest)
        .replace("\"atoms\": [", r#""atoms": [
          {"id":"p-choice","subject":"p","field":"Reservations.State.choice","value":{"some":["v","p"]},"origin":"model"},
          {"id":"q-choice","subject":"q","field":"Reservations.State.choice","value":{"none":true},"origin":"model"},
          {"id":"p-members","subject":"p","field":"Reservations.State.members","value":[["v","p"],["v","q"],["v","p"]],"origin":"model"},
          {"id":"q-members","subject":"q","field":"Reservations.State.members","value":[],"origin":"model"},
          {"id":"p-enabled","subject":"p","field":"Reservations.State.enabled","value":true,"origin":"model"},
        "#);
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}

fn flow_value(subject: &str) -> Scalar {
    Scalar::Subject {
        snapshot: "v".into(),
        subject: subject.into(),
        entity: "Reservations.State".into(),
    }
}

#[test]
fn ordinary_comprehension_owned_family_option_filter_uses_local_producers() {
    use std::{cell::Cell, rc::Rc};
    let active = Rc::new(Cell::new(false));
    let materializations = Rc::new(Cell::new(0));
    let analyses = Rc::new(Cell::new(0));
    let prepared = prepare_observed(
        comprehension_flow_sources(),
        &["selected=evaluate(Reservations.selected,a=@v/A,p=@v/p)"],
        &quiet(),
    )
    .unwrap();
    let Signature::View { body, .. } =
        prepared.inputs().law().declarations()["Reservations.selected"].signature
    else {
        unreachable!()
    };
    let span = prepared.inputs().law().exprs()[body].span;
    let (armed, flats, sources) = (active.clone(), materializations.clone(), analyses.clone());
    data::observe_iterations(move |at, context, phase, _| {
        if at == span && phase == "comprehension_iteration" {
            armed.set(true);
        }
        if phase == "support_materialize" && armed.get() {
            flats.set(flats.get() + 1);
        }
        if phase == "source_analysis" && context.iteration.is_some() {
            sources.set(sources.get() + 1);
        }
        if at == span && phase == "ordinary_evaluation" {
            armed.set(false);
        }
    });
    let result = evaluate_observed(prepared, &quiet()).unwrap();
    data::clear_iteration_observer();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    assert_eq!(result.iterations.len(), 2);
    assert_eq!(
        materializations.get(),
        0,
        "Ref/Option field, Some, Eq and binder retain shared Family support"
    );
    assert_eq!(
        analyses.get(),
        0,
        "the filter is not independently expanded with the full Family per member"
    );
    assert_eq!(
        data_scalar_at(&result, result.answers[0].outputs["value"].0),
        &Scalar::Set {
            element: Type::Ref("Reservations.State".into()),
            items: vec![flow_value("p")]
        }
    );
    let root = result.answers[0].outputs["evaluation"].0;
    let support = result.nodes[root].support.materialize_for_test();
    for id in ["p-owner", "q-owner", "r-owner", "s-owner", "p-choice"] {
        assert!(
            support.iter().any(|fact| fact.atom.as_deref() == Some(id)),
            "retain Family inclusion/exclusion evidence {id}"
        );
    }
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    for change in 0..5 {
        let mut nodes = result.nodes.clone();
        match change {
            0 | 1 => {
                let Some(Payload::Evaluation { parts, .. }) = &mut nodes[root].payload else {
                    unreachable!()
                };
                if change == 0 {
                    parts[0].children.pop();
                } else {
                    parts[0].children.swap(1, 2);
                }
            }
            2 => {
                nodes[root].scope.snapshots.clear();
            }
            3 => {
                nodes[root].support.materialize_mut_for_test().pop();
            }
            _ => {
                let domain = result.iterations[0].finite.unwrap().0;
                let Some(Payload::Domain { elements, .. }) = &mut nodes[domain].payload else {
                    unreachable!()
                };
                elements.pop();
                nodes[domain].arguments.pop();
            }
        }
        rejects_named_prefix(&result, &nodes);
    }
    let mut changed = result;
    let original = changed.iterations[0].clone();
    changed.iterations[0].producer = changed.iterations[1].producer;
    rejects_named_prefix(&changed, &changed.nodes);
    changed.iterations[0] = original;
    let body = changed
        .contexts
        .iter()
        .position(|context| context.iteration == Some(0))
        .unwrap();
    changed.contexts[body].iteration = Some(1);
    rejects_named_prefix(&changed, &changed.nodes);
}

#[test]
fn ordinary_comprehension_list_duplicates_empty_unknown_and_missing_filter_stay_distinct() {
    let sources = comprehension_flow_sources();
    for (subject, expected, iterations) in [
        (
            "p",
            Some(vec![flow_value("p"), flow_value("q"), flow_value("p")]),
            3,
        ),
        ("q", Some(vec![]), 0),
        ("r", None, 0),
    ] {
        let ask = format!("members=evaluate(Reservations.members,p=@v/{subject})");
        let result = evaluate_observed_bytes(sources.clone(), &[&ask], &quiet()).unwrap();
        assert_ne!(result.status(), "error", "{:?}", result.issues);
        assert_eq!(result.iterations.len(), iterations);
        match expected {
            Some(items) => assert_eq!(
                data_scalar_at(&result, result.answers[0].outputs["value"].0),
                &Scalar::List {
                    element: Type::Ref("Reservations.State".into()),
                    items
                }
            ),
            None => {
                assert!(!result.answers[0].outputs.contains_key("value"));
                assert!(result.answers[0].reasons.iter().any(|reason| {
                    reason.missing.iter().any(|fact| {
                        fact.subject == "r"
                            && fact.field.as_deref() == Some("Reservations.State.members")
                    })
                }));
            }
        }
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        if subject == "p" {
            assert_eq!(
                result.iterations[0].member,
                super::super::call::Member::ListPosition(0)
            );
            assert_eq!(
                result.iterations[2].member,
                super::super::call::Member::ListPosition(2)
            );
            assert_ne!(result.iterations[0].producer, result.iterations[2].producer);
            assert_eq!(
                data_scalar_at(&result, result.iterations[0].producer.unwrap().0),
                data_scalar_at(&result, result.iterations[2].producer.unwrap().0)
            );
        }
    }
    let result = evaluate_observed_bytes(
        sources.clone(),
        &["filtered=evaluate(Reservations.filtered,p=@v/p)"],
        &quiet(),
    )
    .unwrap();
    assert!(!result.answers[0].outputs.contains_key("value"));
    assert_eq!(
        result
            .iterations
            .iter()
            .filter(|record| record.caller.case.is_none())
            .count(),
        3
    );
    assert!(result.answers[0].reasons.iter().any(|reason| {
        reason.missing.iter().any(|fact| {
            fact.subject == "q" && fact.field.as_deref() == Some("Reservations.State.enabled")
        })
    }));
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    let nested = evaluate_observed_bytes(
        sources,
        &["nested=evaluate(Reservations.nested,a=@v/A,p=@v/p)"],
        &quiet(),
    )
    .unwrap();
    assert_eq!(
        data_scalar_at(&nested, nested.answers[0].outputs["value"].0),
        &Scalar::List {
            element: Type::Ref("Reservations.State".into()),
            items: vec![flow_value("p"), flow_value("p")]
        }
    );
    rebuild_for_origin_and_support_recheck(&nested, &nested.nodes).unwrap();
}

#[test]
fn ordinary_comprehension_stop_after_member_commit_keeps_a_raw_checkable_prefix() {
    use std::{cell::Cell, rc::Rc};
    for signal in [Signal::Int, Signal::Term] {
        let armed = Rc::new(Cell::new(false));
        let stop = armed.clone();
        let control = Control::new(move |_| stop.replace(false).then_some(signal));
        let seen = armed.clone();
        data::observe_iterations(move |_, context, phase, _| {
            if context.iteration.is_some() && phase == "ordinary_evaluation" {
                seen.set(true);
            }
        });
        let result = evaluate_observed_bytes(
            comprehension_flow_sources(),
            &["members=evaluate(Reservations.members,p=@v/p)"],
            &control,
        )
        .unwrap();
        data::clear_iteration_observer();
        assert!(
            result.answers[0]
                .reasons
                .iter()
                .any(|reason| matches!(reason.kind,ReasonKind::Stop(actual) if actual==signal))
        );
        assert!(!result.iterations.is_empty());
        assert!(
            result
                .nodes
                .iter()
                .any(|node| matches!(node.rule, Rule::BinderValue(_)))
        );
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    }
}
