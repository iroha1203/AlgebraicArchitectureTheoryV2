mod known_map_fixture {
    include!("../../../../tests/common/known_map.rs");
}
fn known_map_private_inputs() -> InputSources {
    let definitions = known_map_fixture::DEFINITIONS.as_bytes();
    let d = archsig_input::definition::check_definitions(&[("definition0", definitions)]).unwrap();
    let digest = &d.vocabularies()["Maps"].digest;
    InputSources::from_bytes(
        vec![definitions.to_vec()],
        known_map_fixture::law(digest).into_bytes(),
        known_map_fixture::archmap(digest, "r1").into_bytes(),
    )
}
fn known_map_private_result(asks: &[&str]) -> ObservedEvaluation {
    let control = quiet();
    let p = prepare_observed(known_map_private_inputs(), asks, &control).unwrap();
    evaluate_observed(p, &control).unwrap()
}
fn known_map_private_atom(r: &ObservedEvaluation) -> usize {
    let value = r.answers[0].outputs["value"];
    let node = &r.nodes[value.0];
    let subject = r.prepared.inputs().archmap().snapshots()[0]
        .subjects
        .iter()
        .find(|subject| subject.id == "s")
        .unwrap();
    let field = subject
        .fields
        .iter()
        .find(|field| field.name == "Maps.Sample.m")
        .unwrap();
    let Slot::Known { pointer, .. } = &field.slot else {
        panic!("observed Map slot")
    };
    assert!(matches!((node.scalar_payload(), &node.rule),
        (Some(Scalar::Map { pairs, .. }), Rule::FieldValue { kind: "atom", location: Some(Location::ArchMap { pointer: actual, span: None }) })
            if !pairs.is_empty() && actual == pointer));
    let [source, base] = node.arguments.as_slice() else {
        panic!("actual field source/base")
    };
    let Some(Payload::Expression {
        location: Location::Law { span },
        ..
    }) = &r.nodes[source.0].payload
    else {
        panic!("Map source")
    };
    assert_eq!(
        &r.prepared.inputs().sources().law().bytes()[span.0..span.1],
        b"s.m"
    );
    let Some(Payload::Evaluation {
        value: Some(owner), ..
    }) = &r.nodes[base.0].payload
    else {
        panic!("Map base")
    };
    assert!(
        matches!(r.nodes[owner.0].scalar_payload(), Some(Scalar::Subject { snapshot, subject, entity }) if snapshot == "v" && subject == "s" && entity == "Maps.Sample")
    );
    assert!(r.nodes.iter().any(|evaluation| matches!(&evaluation.payload,
        Some(Payload::Evaluation { expression, parts, value: Some(actual), .. })
            if expression == source && *actual == value && parts.len() == 1 && parts[0].children == [*base])));
    value.0
}

#[test]
fn quantified_map_reads_share_payload_and_keep_each_source() {
    use std::{cell::Cell, collections::BTreeSet, rc::Rc};

    let inputs = known_map_private_inputs();
    let law = std::str::from_utf8(inputs.law().bytes()).unwrap();
    let (reading, _) = law.rsplit_once('}').unwrap();
    let law = format!(
        "{reading} view repeated(s:Sample,x:Item):Bool = forall q:Bool . (s.m(x)=s.n(x)) and (s.n(x)=s.m(x)); }}"
    );
    let inputs = InputSources::from_bytes(
        vec![inputs.definitions()[0].bytes().to_vec()],
        law.into_bytes(),
        inputs.archmap().bytes().to_vec(),
    );
    let counts = Rc::new(Cell::new((0, 0, 0)));
    let seen = counts.clone();
    data::observe_iterations(move |_, _, operation, i| {
        let (rows, args, copied) = seen.get();
        match operation {
            "map_input_row" => seen.set((rows + 1, args, copied)),
            "map_composite_copy" => seen.set((rows, args + 1, copied + i)),
            _ => {}
        }
    });
    let result = evaluate_observed_bytes(
        inputs,
        &["q=evaluate(Maps.repeated,s=@v/s,x=@v/a)"],
        &quiet(),
    );
    data::clear_iteration_observer();
    let result = result.unwrap();
    let (built_rows, composite_arguments, copied_arrays) = counts.get();
    eprintln!(
        "(built rows, map arguments, deep-copied arrays) {:?}",
        counts.get()
    );
    assert_eq!(built_rows, 4);
    assert_eq!(composite_arguments, 8);
    assert_eq!(copied_arrays, 0);
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    assert_eq!(
        data_scalar_at(&result, result.answers[0].outputs["value"].0),
        &Scalar::Bool(true)
    );

    let mut map_reads = BTreeMap::<_, Vec<_>>::new();
    for (index, node) in result.nodes.iter().enumerate() {
        let (Rule::Input { kind: "atom", .. }, Some(Scalar::Map { pairs, .. })) =
            (&node.rule, node.scalar_payload())
        else {
            continue;
        };
        let facts = node.support.materialize_for_test();
        let [fact] = facts.as_slice() else {
            panic!("Map atom の元支持")
        };
        let atom = fact.atom.as_ref().unwrap().clone();
        map_reads.entry(atom).or_default().push((index, pairs));
    }
    let counts: Vec<_> = map_reads
        .iter()
        .map(|(atom, reads)| {
            let allocations = reads
                .iter()
                .map(|(_, pairs)| pairs.as_ptr())
                .collect::<BTreeSet<_>>();
            (atom.as_str(), reads.len(), allocations.len())
        })
        .collect();
    eprintln!("(Map atom, reads, retained row allocations) {counts:?}");
    assert_eq!(map_reads.len(), 2);
    for atom in ["m", "n"] {
        let reads = &map_reads[atom];
        assert_eq!(reads.len(), 4);
        let mut iterations = BTreeSet::new();
        for (index, pairs) in reads {
            assert_eq!(
                pairs.as_ptr(),
                reads[0].1.as_ptr(),
                "同じ入力 Map の行を共有する"
            );
            iterations.insert(result.contexts[*index].iteration.unwrap());
        }
        assert_eq!(iterations.len(), 2);
    }
    assert_ne!(map_reads["m"][0].1.as_ptr(), map_reads["n"][0].1.as_ptr());
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
}

fn known_map_private_change(value: &mut Scalar) {
    let Scalar::Map { pairs, .. } = value else {
        panic!("map")
    };
    let Scalar::Subject { subject, .. } = &mut pairs[0].1 else {
        panic!("ref")
    };
    assert_eq!(subject, "a");
    *subject = "b".into();
}
#[test]
fn known_map_rechecks_original_pairs_types_support_and_scope() {
    let r = known_map_private_result(&["a=evaluate(Maps.read,s=@v/s)"]);
    assert_eq!(r.status(), "complete");
    let t = known_map_private_atom(&r);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes[..=t]).unwrap();
    completion_mutation(&r, t, |nodes| {
        let Some(value) = nodes[t].scalar_payload_mut() else {
            unreachable!()
        };
        known_map_private_change(value);
    });
    completion_mutation(&r, t, |nodes| {
        let Some(Scalar::Map { pairs, .. }) = nodes[t].scalar_payload_mut() else {
            unreachable!()
        };
        pairs[0].0 = pairs[1].0.clone();
    });
    completion_mutation(&r, t, |nodes| {
        let Some(Scalar::Map { codomain, .. }) = nodes[t].scalar_payload_mut() else {
            unreachable!()
        };
        *codomain = "Maps.Void".into();
    });
    completion_mutation(&r, t, |nodes| {
        nodes[t].support.materialize_mut_for_test().clear();
    });
    completion_mutation(&r, t, |nodes| {
        nodes[t].scope.modes.clear();
    });
}
#[test]
fn known_map_row_permutation_is_accepted_as_the_same_original_function() {
    let r = known_map_private_result(&["a=evaluate(Maps.read,s=@v/s)"]);
    let t = known_map_private_atom(&r);
    let mut nodes = r.nodes.clone();
    let Some(Scalar::Map { pairs, .. }) = nodes[t].scalar_payload_mut() else {
        unreachable!()
    };
    pairs.reverse();
    assert_ne!(format!("{:?}", nodes[t]), format!("{:?}", r.nodes[t]));
    rebuild_for_origin_and_support_recheck(&r, &nodes[..=t]).unwrap();
    rebuild_for_origin_and_support_recheck(&r, &nodes).unwrap();
}
fn known_map_private_stop(after_answer: bool) {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "prior=check(Maps.prior)",
        "current=evaluate(Maps.equal,s=@v/s)",
        "later=evaluate(Maps.seed)",
    ];
    let normal = known_map_private_result(&asks);
    let expected = archsig_input::result::Signal::Term;
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (arm, count, freeze) = (armed.clone(), probes.clone(), frozen.clone());
    let control = Control::new(move |_| {
        count.set(count.get() + 1);
        if arm.replace(false) {
            assert!(freeze.replace(Some(count.get())).is_none());
            Some(archsig_input::result::Signal::Term)
        } else {
            None
        }
    });
    let prepared = prepare_observed(known_map_private_inputs(), &asks, &control).unwrap();
    let law = prepared.inputs().sources().law().bytes().to_vec();
    let stopped = evaluate_observed_with_validator(
        prepared,
        &control,
        |environment, graph, request, answer| {
            environment.validate_answer(graph, request, answer)?;
            if request.id == "prior" && !after_answer {
                let (arm, seen, law) = (armed.clone(), seen.clone(), law.clone());
                data::observe_iterations(move |span, context, operation, _| {
                    if context.request == 1
                        && operation == "ordinary_source"
                        && &law[span.0..span.1] == b"s.m=s.n"
                    {
                        assert!(!seen.replace(true));
                        arm.set(true);
                    }
                });
            }
            if request.id == "current" && after_answer {
                assert!(!seen.replace(true));
                armed.set(true);
            }
            Ok(())
        },
    );
    data::clear_iteration_observer();
    let stopped = stopped.unwrap();
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(control.stop_reason(), Some(expected));
    assert_eq!(stopped.answers[0].status, Decision::Refuted);
    assert_eq!(
        format!("{:?}", stopped.answers[0]),
        format!("{:?}", normal.answers[0])
    );
    if after_answer {
        assert_eq!(stopped.answers[1].status, Decision::Established);
        assert_eq!(
            format!("{:?}", stopped.answers[1]),
            format!("{:?}", normal.answers[1])
        );
    }
    for answer in &stopped.answers[if after_answer { 2 } else { 1 }..] {
        assert_eq!(answer.status, Decision::Undetermined);
        assert!(answer.outputs.is_empty() && answer.evidence.is_empty() && answer.claim.is_none());
        let reason = answer
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s) if s==&expected))
            .unwrap();
        let Json::Obj(ref actual) = reason.wire() else {
            unreachable!()
        };
        let Json::Obj(ref expected) = expected.issue() else {
            unreachable!()
        };
        assert_eq!(actual["details"], expected["details"]);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}

#[test]
fn known_map_stops_preserve_prefix_prior_refutation_and_verified_answer() {
    known_map_private_stop(false);
    known_map_private_stop(true);
}

#[test]
fn owned_map_wrapper_values_recheck_original_nested_types_and_owner_sources() {
    let definitions = known_map_fixture::OWNED_DEFINITIONS.as_bytes();
    let d = archsig_input::definition::check_definitions(&[("definition0", definitions)]).unwrap();
    let digest = &d.vocabularies()["Maps"].digest;
    let input = InputSources::from_bytes(
        vec![definitions.to_vec()],
        known_map_fixture::owned_law(digest).into_bytes(),
        known_map_fixture::owned_archmap(digest).into_bytes(),
    );
    let control = quiet();
    let prepared = prepare_observed(input, &["a=evaluate(Maps.tables,s=@v/h)"], &control).unwrap();
    let result = evaluate_observed(prepared, &control).unwrap();
    assert_eq!(result.status(), "complete");
    let holder = result.prepared.inputs().archmap().snapshots()[0]
        .subjects
        .iter()
        .find(|subject| subject.id == "h")
        .unwrap();
    let field = holder
        .fields
        .iter()
        .find(|field| field.name == "Maps.Holder.tables")
        .unwrap();
    let Slot::Known { pointer, .. } = &field.slot else {
        panic!("observed tables slot")
    };
    let location = Location::ArchMap {
        pointer: pointer.clone(),
        span: None,
    };
    let target = result.nodes.iter().position(|node| {
        matches!((node.scalar_payload(), &node.rule),
            (Some(Scalar::List { items, .. }), Rule::FieldValue { kind: "atom", location: Some(actual) }) if !items.is_empty() && *actual == location)
    }).expect("actual tables FieldValue at its original atom pointer");
    let [source, base] = result.nodes[target].arguments.as_slice() else {
        panic!("actual Source/base refs")
    };
    let Some(Payload::Expression {
        location: Location::Law { span },
        ..
    }) = &result.nodes[source.0].payload
    else {
        panic!("tables source")
    };
    assert_eq!(
        &result.prepared.inputs().sources().law().bytes()[span.0..span.1],
        b"s.tables"
    );
    let Some(Payload::Evaluation {
        value: Some(owner), ..
    }) = &result.nodes[base.0].payload
    else {
        panic!("tables base")
    };
    assert!(
        matches!(result.nodes[owner.0].scalar_payload(), Some(Scalar::Subject { snapshot, subject, entity }) if snapshot == "v" && subject == "h" && entity == "Maps.Holder")
    );
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
    completion_mutation(&result, target, |nodes| {
        let Some(Scalar::List { element, .. }) = nodes[target].scalar_payload_mut() else {
            unreachable!()
        };
        *element = Type::Map(
            Box::new(Type::Owned("Maps.Item".into(), "owner".into())),
            Box::new(Type::Owned("Maps.Item".into(), "owner".into())),
        );
    });
    completion_mutation(&result, target, |nodes| {
        let Some(Scalar::List { items, .. }) = nodes[target].scalar_payload_mut() else {
            unreachable!()
        };
        let Scalar::Map { pairs, .. } = &mut items[0] else {
            unreachable!()
        };
        let Scalar::Subject { snapshot, .. } = &mut pairs[0].1 else {
            unreachable!()
        };
        *snapshot = "other".into();
    });
    completion_mutation(&result, target, |nodes| {
        nodes[target].support.materialize_mut_for_test().clear();
    });
    completion_mutation(&result, target, |nodes| {
        nodes[target].scope.snapshots.clear();
    });
    let holder = result.prepared.inputs().archmap().snapshots()[0]
        .subjects
        .iter()
        .find(|s| s.id == "h")
        .unwrap();
    let field = holder
        .fields
        .iter()
        .find(|f| f.name == "Maps.Holder.tables")
        .unwrap();
    assert!(
        matches!(&field.ty,Type::List(t) if matches!(t.as_ref(),Type::Map(a,b) if matches!(a.as_ref(),Type::Owned(n,o) if n=="Maps.Item"&&o=="owner")&&matches!(b.as_ref(),Type::Owned(n,o) if n=="Maps.Item"&&o=="owner")))
    );
}

#[test]
fn inherited_map_reads_keep_the_expanded_snapshot_and_atom() {
    let fixture = |file| match file {
        "definitions" => {
            include_bytes!("../../../../tests/fixtures/inherited-map/definitions.json").as_slice()
        }
        "law" => include_bytes!("../../../../tests/fixtures/inherited-map/laws.law").as_slice(),
        _ => include_bytes!("../../../../tests/fixtures/inherited-map/archmap.json").as_slice(),
    };
    for view in ["read", "direct"] {
        for snapshots in [["v", "w"], ["w", "v"]] {
            let asks = snapshots
                .map(|snapshot| format!("{snapshot}=evaluate(Maps.{view},s=@{snapshot}/h)"));
            let inputs = InputSources::from_bytes(
                vec![fixture("definitions").to_vec()],
                fixture("law").to_vec(),
                fixture("archmap").to_vec(),
            );
            let result =
                evaluate_observed_bytes(inputs, &asks.each_ref().map(String::as_str), &quiet())
                    .unwrap();
            assert_eq!(
                result.status(),
                "complete",
                "{view} {snapshots:?}: {:?}",
                result.issues
            );
            for (answer, snapshot) in result.answers.iter().zip(snapshots) {
                let value = answer.outputs["value"].0;
                let Scalar::Map { pairs, .. } = data_scalar_at(&result, value) else {
                    panic!("観測Map")
                };
                let [(key, image)] = pairs.as_slice() else {
                    panic!("1行のMap")
                };
                for endpoint in [key, image] {
                    assert!(
                        matches!(endpoint, Scalar::Subject { snapshot: actual, subject, .. }
                        if actual == snapshot && subject == "a")
                    );
                }
                assert!(
                    result.nodes[value]
                        .support
                        .materialize_for_test()
                        .into_iter()
                        .any(|fact| fact.snapshot == snapshot
                            && fact.subject == "h"
                            && fact.atom.as_deref() == Some("tables"))
                );
            }
            rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        }
    }
}

#[test]
fn quantified_nested_observation_does_not_rebuild_its_map_rows() {
    use std::{cell::Cell, rc::Rc};

    let definition = known_map_fixture::OWNED_DEFINITIONS.as_bytes();
    let checked =
        archsig_input::definition::check_definitions(&[("definition0", definition)]).unwrap();
    let digest = &checked.vocabularies()["Maps"].digest;
    let law = known_map_fixture::owned_law(digest);
    let (reading, _) = law.rsplit_once('}').unwrap();
    let law = format!(
        "{reading} view repeated(s:Holder):Bool = forall q:Bool . (s.tables=s.tables) and (s.tables=s.tables); }}"
    );
    let inputs = InputSources::from_bytes(
        vec![definition.to_vec()],
        law.into_bytes(),
        known_map_fixture::owned_archmap(digest).into_bytes(),
    );
    let builds = Rc::new(Cell::new(0));
    let seen = builds.clone();
    data::observe_iterations(move |_, _, operation, _| {
        if operation == "map_input_row" {
            seen.set(seen.get() + 1);
        }
    });
    let result = evaluate_observed_bytes(inputs, &["q=evaluate(Maps.repeated,s=@v/h)"], &quiet());
    data::clear_iteration_observer();
    let result = result.unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    assert_eq!(
        data_scalar_at(&result, result.answers[0].outputs["value"].0),
        &Scalar::Bool(true)
    );
    assert_eq!(builds.get(), 1);
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
}
