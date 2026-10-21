use archsig::{
    canonical::Json,
    construction::{
        ConstructionFailure, construct,
        maps::{
            DeclarationCorrespondence, ObjectViewTransport, ObjectViewTransportFailure as Error,
            ViewConditionFailure as Failed, ViewTransportOutcome as Outcome, ViewValueEquivalence,
            correspondence, declaration_correspondence, object_view_transport,
        },
        readings::{ObjectEvaluationOutcome, object_reading_instances},
    },
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        input::{CheckedInputs, InputSources, check_inputs},
    },
    result::Signal,
};
use std::{cell::Cell, rc::Rc, sync::Arc};
const D: &[u8] = include_bytes!("fixtures/object-view-transport.atoms.json");
const L: &str = include_str!("fixtures/object-view-transport.law");
const A: &str = include_str!("fixtures/object-view-transport.archmap.json");
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn inputs(law: &str, map: &str) -> Arc<CheckedInputs> {
    let right = include_bytes!("fixtures/configuration-map-right.atoms.json");
    let defs = archsig::definition::check_definitions(&[("left", D), ("right", right)]).unwrap();
    let ld = &defs.vocabularies["Left"].digest;
    let rd = &defs.vocabularies["Right"].digest;
    let bridge = include_str!("fixtures/configuration-map-bridge.atoms.json")
        .replace("@LEFT_DIGEST@", ld)
        .replace("@RIGHT_DIGEST@", rd);
    let defs = archsig::definition::check_definitions(&[
        ("left", D),
        ("right", right),
        ("bridge", bridge.as_bytes()),
    ])
    .unwrap();
    let expand = |s: &str| {
        s.replace("@LEFT_DIGEST@", ld)
            .replace("@RIGHT_DIGEST@", rd)
            .replace("@BRIDGE_DIGEST@", &defs.vocabularies["Bridge"].digest)
            .into_bytes()
    };
    Arc::new(
        check_inputs(
            InputSources::from_bytes(
                vec![D.to_vec(), right.to_vec(), bridge.into_bytes()],
                expand(law),
                expand(map),
            ),
            &mut quiet(),
        )
        .unwrap_or_else(|f| panic!("{:?}", f.issues())),
    )
}
fn declarations(i: &CheckedInputs) -> DeclarationCorrespondence {
    let r = correspondence(i, "v", "m", "Before", Some("After"), &mut quiet()).unwrap();
    assert!(r.missing().is_empty(), "{:?}", r.missing());
    assert!(r.counterexamples().is_empty(), "{:?}", r.counterexamples());
    declaration_correspondence(i, r.map().unwrap(), &mut quiet()).unwrap()
}
fn indices(i: &CheckedInputs, object: &str, view: &str, subject: &str) -> (usize, usize) {
    let c = construct(i, "Before", "v", "a", &mut quiet()).unwrap();
    let p = object_reading_instances(i, &c, &mut quiet()).unwrap();
    (
        p.objects()
            .iter()
            .position(|o| o.identity().subject().subject == object)
            .unwrap(),
        p.instances()
            .iter()
            .position(|r| {
                r.declaration().name == format!("Before.{view}")
                    && r.bindings()
                        .iter()
                        .any(|b| b.parameter().name == "c" && b.subject().subject == subject)
            })
            .unwrap(),
    )
}
fn run(i: Arc<CheckedInputs>, object: &str, view: &str, subject: &str) -> ObjectViewTransport {
    let d = declarations(&i);
    let (o, r) = indices(&i, object, view, subject);
    object_view_transport(i, &d, o, r, &mut quiet()).unwrap()
}
fn f<'a>(j: &'a Json, k: &str) -> &'a Json {
    let Json::Obj(m) = j else { panic!("{j:?}") };
    &m[k]
}
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(a) = j else { panic!("{j:?}") };
    a
}
fn edit(map: &str, id: &str, before: &str, after: &str) -> String {
    let key = format!("\"id\":\"{id}\"");
    assert_eq!(map.lines().filter(|l| l.contains(&key)).count(), 1);
    map.lines()
        .map(|l| {
            if l.contains(&key) {
                assert!(l.contains(before));
                l.replace(before, after)
            } else {
                l.into()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}
fn remove(map: &str, id: &str) -> String {
    let key = format!("\"id\":\"{id}\"");
    assert_eq!(map.lines().filter(|l| l.contains(&key)).count(), 1);
    map.lines()
        .filter(|l| !l.contains(&key))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]")
}
#[test]
fn actual_numeric_values_commute_and_false_is_an_ordinary_value() {
    let i = inputs(L, A);
    for (view, expected) in [
        ("amount", "\"2\""),
        ("ratio", "[\"1\",\"2\"]"),
        ("flag", "false"),
    ] {
        let r = run(Arc::clone(&i), "p", view, "p");
        assert_eq!(r.outcome(), &Outcome::Preserved);
        assert_eq!(r.source_value().unwrap().wire().canonical(), expected);
        assert_eq!(r.image().unwrap().wire().canonical(), expected);
        assert_eq!(r.target_value().unwrap().wire().canonical(), expected);
        assert_eq!(r.target_object().unwrap().subject().subject, "q");
        assert_eq!(
            r.target_instance().unwrap().declaration().name,
            format!("After.{view}")
        );
        for e in [r.source().unwrap(), r.target().unwrap()] {
            let ObjectEvaluationOutcome::Evaluated(e) = e.outcome() else {
                panic!()
            };
            assert!(Arc::ptr_eq(&i, &e.prepared().shared_inputs()));
        }
        r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
    }
}
#[test]
fn reference_and_composite_values_use_value_maps_instead_of_atom_outside_action() {
    let i = inputs(L, A);
    for (view, source, target) in [
        ("ref", "[\"v\",\"p\"]", "[\"v\",\"q\"]"),
        (
            "packed",
            "[{\"some\":[\"v\",\"p\"]},false]",
            "[{\"some\":[\"v\",\"q\"]},false]",
        ),
        ("external", "[\"v\",\"m\"]", "[\"v\",\"m\"]"),
    ] {
        let r = run(Arc::clone(&i), "p", view, "p");
        assert_eq!(r.outcome(), &Outcome::Preserved);
        assert_eq!(r.source_value().unwrap().wire().canonical(), source);
        assert_eq!(r.image().unwrap().wire().canonical(), target);
        assert_eq!(r.target_value().unwrap().wire().canonical(), target);
        assert!(matches!(
            r.equivalence(),
            Some(ViewValueEquivalence::Finite(_))
        ));
        if view == "external" {
            assert_eq!(
                r.objects()
                    .action()
                    .image(&archsig::construction::FactPointer {
                        snapshot: "v".into(),
                        subject: "m".into(),
                        field: None,
                        atom: None
                    })
                    .unwrap()
                    .subject,
                "b"
            );
        }
    }
}
#[test]
fn unequal_values_keep_both_evaluations_original_support_and_operation() {
    let i = inputs(L, A);
    let r = run(Arc::clone(&i), "r", "amount", "r");
    assert_eq!(r.outcome(), &Outcome::Refuted(Failed::Value));
    assert_eq!(r.source_value().unwrap().wire(), Json::str("3"));
    assert_eq!(r.image().unwrap().wire(), Json::str("3"));
    assert_eq!(r.target_value().unwrap().wire(), Json::str("2"));
    r.operation().recheck(&i, &mut quiet()).unwrap();
    let r = run(Arc::clone(&i), "p", "amount", "p");
    let ObjectEvaluationOutcome::Evaluated(e) = r.source().unwrap().outcome() else {
        panic!()
    };
    let w = e.wire();
    let answer = &arr(f(&w, "answers"))[0];
    let value = f(f(f(answer, "outputs"), "value"), "node");
    let node = arr(f(&w, "nodes"))
        .iter()
        .find(|n| f(n, "id") == value)
        .unwrap();
    assert!(
        arr(f(node, "support"))
            .iter()
            .any(|fct| fct.canonical().contains("p-count"))
    );
    let atom = i.archmap().snapshots[0]
        .subjects
        .iter()
        .find(|s| s.id == "p")
        .unwrap()
        .fields
        .iter()
        .find(|f| f.name == "Left.Child.count")
        .unwrap();
    let archsig::archmap::Slot::Known { origin, .. } = &atom.slot else {
        panic!()
    };
    let origin = i
        .archmap()
        .origins
        .iter()
        .find(|o| &o.id == origin)
        .unwrap();
    let source = i
        .archmap()
        .sources
        .iter()
        .find(|s| s.id == origin.locations[0].source)
        .unwrap();
    assert_eq!(source.uri, "urn:fixture:view-amount");
    assert_eq!(source.revision, "amount-r1");
}
#[test]
fn absent_axes_and_unknown_membership_differ_from_missing_observed_values() {
    let i = inputs(L, A);
    let r = run(Arc::clone(&i), "p", "flag", "r");
    assert_eq!(r.outcome(), &Outcome::Preserved);
    assert!(r.image().is_none());
    assert!(matches!(
        r.source().unwrap().outcome(),
        ObjectEvaluationOutcome::NotApplicable
    ));
    assert!(matches!(
        r.target().unwrap().outcome(),
        ObjectEvaluationOutcome::NotApplicable
    ));
    let r = run(Arc::clone(&i), "p", "conditional", "p");
    assert_eq!(r.outcome(), &Outcome::Undetermined);
    for e in [r.source().unwrap(), r.target().unwrap()] {
        let ObjectEvaluationOutcome::Conditional(c) = e.outcome() else {
            panic!("{:?}", e.outcome())
        };
        assert!(c.iter().any(|c| c.slot().subject == "y"
            && c.slot().field.as_deref() == Some("Left.ExternalChild.owner")));
    }
    let i = inputs(L, &remove(A, "p-count"));
    let r = run(Arc::clone(&i), "p", "amount", "p");
    assert_eq!(r.outcome(), &Outcome::Undetermined);
    assert!(r.source_value().is_none());
    assert!(r.image().is_none());
    assert_eq!(r.target_value().unwrap().wire(), Json::str("2"));
    let ObjectEvaluationOutcome::Evaluated(e) = r.source().unwrap().outcome() else {
        panic!()
    };
    assert_eq!(e.status(), "partial");
    assert!(e.wire().canonical().contains("missing_observation"));
    r.operation().recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn applicability_and_whole_type_equivalence_failures_are_separate_conditions() {
    let a = edit(
        A,
        "m-entries",
        "[[\"v\",\"r\"],[\"v\",\"s\"]]",
        "[[\"v\",\"r\"],[\"v\",\"q\"]]",
    );
    let i = inputs(L, &a);
    let r = run(Arc::clone(&i), "p", "flag", "r");
    assert_eq!(r.outcome(), &Outcome::Refuted(Failed::Applicability));
    r.operation().recheck(&i, &mut quiet()).unwrap();
    let r = run(Arc::clone(&i), "p", "ref", "p");
    assert_eq!(r.outcome(), &Outcome::Refuted(Failed::ValueType));
    let Some(ViewValueEquivalence::Finite(e)) = r.equivalence() else {
        panic!()
    };
    assert!(e.bijection().is_none());
    assert!(!e.failures().is_empty());
    r.operation().recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn missing_declaration_and_unimplemented_families_keep_verified_operation() {
    let i = inputs(&L.replace("view flag(d:", "view different(d:"), A);
    let r = run(Arc::clone(&i), "p", "flag", "p");
    assert_eq!(
        r.outcome(),
        &Outcome::Refuted(Failed::Declaration {
            source: "Before.flag".into()
        })
    );
    r.operation().recheck(&i, &mut quiet()).unwrap();
    let i = inputs(L, A);
    let d = declarations(&i);
    for view in ["family", "sequence"] {
        let (o, r) = indices(&i, "p", view, "p");
        let Error::NotImplemented {
            operation,
            object,
            instance,
            returns,
        } = object_view_transport(Arc::clone(&i), &d, o, r, &mut quiet()).unwrap_err()
        else {
            panic!()
        };
        operation.recheck(&i, &mut quiet()).unwrap();
        assert_eq!(object.subject().subject, "p");
        assert_eq!(instance.declaration().name, format!("Before.{view}"));
        assert_eq!(Some(returns), instance.declaration().returns);
        if view == "family" {
            assert_eq!(instance.parameters().len(), 1);
        }
    }
}
#[test]
fn current_values_mapping_and_law_body_are_rechecked() {
    let i = inputs(L, A);
    let r = run(Arc::clone(&i), "p", "amount", "p");
    for changed in [
        inputs(L, &edit(A, "p-count", "\"value\":\"2\"", "\"value\":\"4\"")),
        inputs(
            &L.replace(
                "view amount(d: Right.Child): Z = 2;",
                "view amount(d: Right.Child): Z = 3;",
            ),
            A,
        ),
        inputs(
            L,
            &edit(
                A,
                "m-entries",
                "[[[\"v\",\"p\"],[\"v\",\"q\"]],[[\"v\",\"r\"],[\"v\",\"s\"]]]",
                "[[[\"v\",\"p\"],[\"v\",\"s\"]],[[\"v\",\"r\"],[\"v\",\"q\"]]]",
            ),
        ),
    ] {
        assert!(r.recheck(changed, &mut quiet()).is_err());
    }
    let d = declarations(&i);
    let (o, n) = indices(&i, "p", "amount", "p");
    for (o, n) in [(usize::MAX, n), (o, usize::MAX)] {
        assert!(matches!(
            object_view_transport(Arc::clone(&i), &d, o, n, &mut quiet()),
            Err(Error::Construction(ConstructionFailure::InvalidSelection(
                _
            )))
        ));
    }
}
#[test]
fn fixed_transport_checkpoints_latch_time_memory_and_cancellation() {
    let i = inputs(L, A);
    let d = declarations(&i);
    let (o, n) = indices(&i, "p", "amount", "p");
    for point in [
        Checkpoint::ObjectViewTransport,
        Checkpoint::ObjectEvaluation,
        Checkpoint::Expression,
    ] {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        object_view_transport(
            Arc::clone(&i),
            &d,
            o,
            n,
            &mut Control::new(Limits::default(), move |p| {
                if p == point {
                    seen.set(seen.get() + 1);
                }
                Usage::default()
            }),
        )
        .unwrap();
        let total = count.get();
        assert!(total > 2);
        let mut positions = vec![1, (total + 1) / 2, total];
        positions.sort();
        positions.dedup();
        for at in positions {
            for mode in 0..4 {
                let count = Rc::new(Cell::new(0));
                let seen = count.clone();
                let mut c = Control::new(
                    Limits {
                        time_ms: Some(1),
                        memory_mib: Some(1),
                    },
                    move |p| {
                        if p == point {
                            seen.set(seen.get() + 1);
                        }
                        let stop = seen.get() >= at;
                        Usage {
                            elapsed_ms: if stop && mode == 0 { 1 } else { 0 },
                            memory_mib: if stop && mode == 1 { 1 } else { 0 },
                            signal: if stop {
                                match mode {
                                    2 => Some(Signal::Int),
                                    3 => Some(Signal::Term),
                                    _ => None,
                                }
                            } else {
                                None
                            },
                        }
                    },
                );
                let failure = object_view_transport(Arc::clone(&i), &d, o, n, &mut c).unwrap_err();
                let reason = match failure {
                    Error::Construction(ConstructionFailure::Stopped(reason)) => reason,
                    Error::Stopped {
                        reason,
                        operation,
                        partial,
                        ..
                    } => {
                        operation.recheck(&i, &mut quiet()).unwrap();
                        if let Some(p) = partial {
                            assert_eq!(p.operation(), operation.as_ref());
                        }
                        reason
                    }
                    failure => panic!("{failure:?}"),
                };
                assert_eq!(reason, c.stop_reason().unwrap());
                assert_eq!(count.get(), at);
                assert!(matches!(
                    object_view_transport(Arc::clone(&i), &d, o, n, &mut c),
                    Err(Error::Construction(ConstructionFailure::Stopped(_)))
                ));
                assert_eq!(count.get(), at);
            }
        }
    }
}

#[test]
fn stopped_transport_keeps_completed_evaluations_values_and_decisions_only() {
    let i = inputs(L, A);
    let d = declarations(&i);
    for (subject, expected) in [
        ("p", Outcome::Preserved),
        ("r", Outcome::Refuted(Failed::Value)),
    ] {
        let (o, n) = indices(&i, subject, "amount", subject);
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let normal = object_view_transport(
            Arc::clone(&i),
            &d,
            o,
            n,
            &mut Control::new(Limits::default(), move |p| {
                if p == Checkpoint::ObjectViewTransport {
                    seen.set(seen.get() + 1);
                }
                Usage::default()
            }),
        )
        .unwrap();
        let total = count.get();
        assert!(total >= 6);
        // source完了直後、target完了直後、比較完了直後でそれぞれ止める。
        for at in [total - 2, total - 1, total] {
            for mode in 0..4 {
                let seen = Rc::new(Cell::new(0));
                let count = seen.clone();
                let mut control = Control::new(
                    Limits {
                        time_ms: Some(1),
                        memory_mib: Some(1),
                    },
                    move |p| {
                        if p == Checkpoint::ObjectViewTransport {
                            count.set(count.get() + 1);
                        }
                        let stop = count.get() >= at;
                        Usage {
                            elapsed_ms: u128::from(stop && mode == 0),
                            memory_mib: u128::from(stop && mode == 1),
                            signal: if stop {
                                match mode {
                                    2 => Some(Signal::Int),
                                    3 => Some(Signal::Term),
                                    _ => None,
                                }
                            } else {
                                None
                            },
                        }
                    },
                );
                let Error::Stopped {
                    reason,
                    operation,
                    partial: Some(partial),
                    evaluation,
                } = object_view_transport(Arc::clone(&i), &d, o, n, &mut control).unwrap_err()
                else {
                    panic!()
                };
                assert_eq!(reason, control.stop_reason().unwrap());
                assert_eq!(seen.get(), at);
                assert!(evaluation.is_none());
                operation.recheck(&i, &mut quiet()).unwrap();
                assert_eq!(partial.operation(), operation.as_ref());
                assert_eq!(partial.object().subject().subject, subject);
                assert_eq!(partial.instance().declaration().name, "Before.amount");
                assert!(partial.equivalence().is_some());
                let ObjectEvaluationOutcome::Evaluated(source) =
                    partial.source().unwrap().outcome()
                else {
                    panic!()
                };
                assert_eq!(source.status(), "complete");
                assert!(Arc::ptr_eq(&i, &source.prepared().shared_inputs()));
                let ObjectEvaluationOutcome::Evaluated(original) =
                    normal.source().unwrap().outcome()
                else {
                    panic!()
                };
                assert_eq!(source.wire(), original.wire());
                let value = if subject == "p" { "\"2\"" } else { "\"3\"" };
                assert_eq!(partial.source_value().unwrap().wire().canonical(), value);
                if at == total - 2 {
                    assert!(partial.target().is_none());
                    assert!(partial.target_value().is_none());
                } else {
                    let ObjectEvaluationOutcome::Evaluated(target) =
                        partial.target().unwrap().outcome()
                    else {
                        panic!()
                    };
                    assert_eq!(target.status(), "complete");
                    assert!(Arc::ptr_eq(&i, &target.prepared().shared_inputs()));
                    let ObjectEvaluationOutcome::Evaluated(original) =
                        normal.target().unwrap().outcome()
                    else {
                        panic!()
                    };
                    assert_eq!(target.wire(), original.wire());
                    assert_eq!(partial.target_value().unwrap().wire().canonical(), "\"2\"");
                }
                if at == total {
                    assert_eq!(partial.image().unwrap().wire().canonical(), value);
                    assert_eq!(partial.outcome(), Some(&expected));
                } else {
                    assert!(partial.image().is_none());
                    assert!(partial.outcome().is_none());
                }
                assert!(matches!(
                    object_view_transport(Arc::clone(&i), &d, o, n, &mut control),
                    Err(Error::Construction(ConstructionFailure::Stopped(_)))
                ));
                assert_eq!(seen.get(), at);
            }
        }
    }
}

#[test]
fn target_expression_stop_keeps_source_and_target_partial_dag_without_a_decision() {
    let i = inputs(L, A);
    let d = declarations(&i);
    let (o, n) = indices(&i, "p", "amount", "p");
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let mut control = Control::new(
        Limits {
            time_ms: Some(1),
            memory_mib: None,
        },
        move |p| {
            if p == Checkpoint::Expression {
                seen.set(seen.get() + 1);
            }
            Usage {
                elapsed_ms: u128::from(seen.get() >= 3),
                ..Usage::default()
            }
        },
    );
    let Error::Stopped {
        operation,
        partial: Some(partial),
        ..
    } = object_view_transport(Arc::clone(&i), &d, o, n, &mut control).unwrap_err()
    else {
        panic!()
    };
    operation.recheck(&i, &mut quiet()).unwrap();
    let ObjectEvaluationOutcome::Evaluated(source) = partial.source().unwrap().outcome() else {
        panic!()
    };
    assert_eq!(source.status(), "complete");
    assert_eq!(partial.source_value().unwrap().wire(), Json::str("2"));
    let ObjectEvaluationOutcome::Evaluated(target) = partial.target().unwrap().outcome() else {
        panic!()
    };
    assert_eq!(target.status(), "interrupted");
    assert!(!arr(f(&target.wire(), "nodes")).is_empty());
    assert!(partial.outcome().is_none());
    assert!(partial.image().is_none());
    assert_eq!(count.get(), 3);
}

#[test]
fn target_object_and_instance_failures_keep_the_base_configuration_operation() {
    let d = include_bytes!("fixtures/cross-kind-transport.atoms.json");
    let defs = archsig::definition::check_definitions(&[("definition0", d)]).unwrap();
    let digest = &defs.vocabularies["V"].digest;
    let law = "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Read { use vocabulary V version \"1\" digest \"@DIGEST@\"; view probe(s: V.S): Bool = false; }";
    let i = Arc::new(
        check_inputs(
            InputSources::from_bytes(
                vec![d.to_vec()],
                law.replace("@DIGEST@", digest).into_bytes(),
                include_str!("fixtures/cross-kind-transport.archmap.json")
                    .replace("@DIGEST@", digest)
                    .into_bytes(),
            ),
            &mut quiet(),
        )
        .unwrap(),
    );
    let c = correspondence(&i, "v", "m", "Read", None, &mut quiet()).unwrap();
    let ds = declaration_correspondence(&i, c.map().unwrap(), &mut quiet()).unwrap();
    let p = object_reading_instances(
        &i,
        &construct(&i, "Read", "v", "A", &mut quiet()).unwrap(),
        &mut quiet(),
    )
    .unwrap();
    let o = p
        .objects()
        .iter()
        .position(|o| o.identity().subject().subject == "s")
        .unwrap();
    let n = p
        .instances()
        .iter()
        .position(|r| {
            r.declaration().name == "Read.probe" && r.bindings()[0].subject().subject == "s"
        })
        .unwrap();
    let r = object_view_transport(Arc::clone(&i), &ds, o, n, &mut quiet()).unwrap();
    assert_eq!(r.outcome(), &Outcome::Refuted(Failed::Object));
    r.operation().recheck(&i, &mut quiet()).unwrap();
    let a=A.replace("\"subjects\":[","\"subjects\":[\n{\"id\":\"z\",\"type\":\"Right.Root\",\"origin\":\"model\"},\n{\"id\":\"u\",\"type\":\"Right.Child\",\"origin\":\"model\"},").replace("\"atoms\":[","\"atoms\":[\n{\"id\":\"u-owner\",\"subject\":\"u\",\"field\":\"Right.Child.owner\",\"value\":[\"v\",\"z\"],\"origin\":\"model\"},");
    let i = inputs(L, &a);
    let p = object_reading_instances(
        &i,
        &construct(&i, "Before", "v", "a", &mut quiet()).unwrap(),
        &mut quiet(),
    )
    .unwrap();
    let o = p
        .objects()
        .iter()
        .position(|o| o.identity().subject().subject == "p")
        .unwrap();
    let n = p
        .instances()
        .iter()
        .position(|r| {
            r.declaration().name == "Before.boundary"
                && r.bindings()
                    .iter()
                    .any(|b| b.parameter().name == "c" && b.subject().subject == "p")
                && r.bindings()
                    .iter()
                    .any(|b| b.parameter().name == "x" && b.subject().subject == "u")
        })
        .unwrap();
    let r = object_view_transport(Arc::clone(&i), &declarations(&i), o, n, &mut quiet()).unwrap();
    let Outcome::Refuted(Failed::TargetInstance {
        declaration,
        bindings,
    }) = r.outcome()
    else {
        panic!("{:?}", r.outcome())
    };
    assert_eq!(declaration, "After.boundary");
    assert!(
        bindings
            .iter()
            .any(|(name, f)| name == "y" && f.subject == "u")
    );
    r.operation().recheck(&i, &mut quiet()).unwrap();
}
