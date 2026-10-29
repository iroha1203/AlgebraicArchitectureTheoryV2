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
    inputs_with_left(D, law, map)
}
fn inputs_with_left(left: &[u8], law: &str, map: &str) -> Arc<CheckedInputs> {
    let right = include_bytes!("fixtures/configuration-map-right.atoms.json");
    let defs = archsig::definition::check_definitions(&[("left", left), ("right", right)]).unwrap();
    let ld = &defs.vocabularies()["Left"].digest;
    let rd = &defs.vocabularies()["Right"].digest;
    let bridge = include_str!("fixtures/configuration-map-bridge.atoms.json")
        .replace("@LEFT_DIGEST@", ld)
        .replace("@RIGHT_DIGEST@", rd);
    let defs = archsig::definition::check_definitions(&[
        ("left", left),
        ("right", right),
        ("bridge", bridge.as_bytes()),
    ])
    .unwrap();
    let expand = |s: &str| {
        s.replace("@LEFT_DIGEST@", ld)
            .replace("@RIGHT_DIGEST@", rd)
            .replace("@BRIDGE_DIGEST@", &defs.vocabularies()["Bridge"].digest)
            .into_bytes()
    };
    Arc::new(
        check_inputs(
            InputSources::from_bytes(
                vec![left.to_vec(), right.to_vec(), bridge.into_bytes()],
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
fn finite_view_family_is_preserved_at_every_boolean_argument() {
    let i = inputs(L, A);
    let d = declarations(&i);
    let (o, r) = indices(&i, "p", "family", "p");
    let result = object_view_transport(Arc::clone(&i), &d, o, r, &mut quiet())
        .expect("Bool parameter の全域でviewの保存を検査する");
    assert_eq!(result.outcome(), &Outcome::Preserved);
    let family = result.family().unwrap();
    assert!(family.is_complete());
    assert_eq!(family.parameters().len(), 1);
    assert_eq!(
        family.parameters()[0].position(),
        archsig::construction::maps::DeclarationValuePosition::Parameter(1)
    );
    assert_eq!(family.parameters()[0].forward(), Some([0, 1].as_slice()));
    assert_eq!(family.rows().len(), 2);
    for (row, expected) in family.rows().iter().zip([false, true]) {
        assert_eq!(row.source_arguments()[0].wire(), Json::Bool(expected));
        assert_eq!(row.target_arguments()[0].wire(), Json::Bool(expected));
        assert_eq!(row.source().unwrap().wire(), Json::Bool(expected));
        assert_eq!(row.image().unwrap().wire(), Json::Bool(expected));
        assert_eq!(row.target().unwrap().wire(), Json::Bool(expected));
        assert_eq!(row.outcome(), &Outcome::Preserved);
    }
    result.operation().recheck(&i, &mut quiet()).unwrap();
    result.recheck(i, &mut quiet()).unwrap();
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
    let law = L
        .replace(
            "List<Z> = list<Z>[c.count]",
            "List<(Z,Left.Child)> = list<(Z,Left.Child)>[(c.count,c)]",
        )
        .replace(
            "List<Z> = list<Z>[2]",
            "List<(Z,Right.Child)> = list<(Z,Right.Child)>[(2,d)]",
        );
    let i = inputs(&law, A);
    let d = declarations(&i);
    let (o, r) = indices(&i, "p", "sequence", "p");
    let Err(Error::NotImplemented {
        operation,
        object,
        instance,
        returns,
        ..
    }) = object_view_transport(Arc::clone(&i), &d, o, r, &mut quiet())
    else {
        panic!("reference container requires a value transport");
    };
    operation.recheck(&i, &mut quiet()).unwrap();
    assert_eq!(object.subject().subject, "p");
    assert_eq!(instance.declaration().name, "Before.sequence");
    assert_eq!(Some(returns), instance.declaration().returns);
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
                    transport: None,
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
    let digest = &defs.vocabularies()["V"].digest;
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

fn stop_at(point: Checkpoint, at: usize, mode: usize) -> (Control, Rc<Cell<usize>>) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let c = Control::new(
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
    (c, count)
}

#[test]
fn stopped_structure_transport_reaches_the_view_caller() {
    let i = inputs(L, A);
    let d = declarations(&i);
    let (o, n) = indices(&i, "p", "amount", "p");
    for point in [
        Checkpoint::InternalArrowRoster,
        Checkpoint::ConfigurationTransportObject,
        Checkpoint::ObjectInstances,
    ] {
        for mode in 0..4 {
            let (mut c, probes) = stop_at(point, 1, mode);
            let Error::Stopped {
                reason,
                operation,
                partial,
                evaluation,
                transport: Some(p),
            } = object_view_transport(Arc::clone(&i), &d, o, n, &mut c).unwrap_err()
            else {
                panic!("構造側の部分結果が必要")
            };
            assert_eq!(reason, c.stop_reason().unwrap());
            assert_eq!(operation.as_ref(), p.operation());
            operation.recheck(&i, &mut quiet()).unwrap();
            assert!(partial.is_none());
            assert!(evaluation.is_none());
            assert_eq!(
                p.outcome(),
                (point == Checkpoint::ObjectInstances).then_some(true)
            );
            assert!(p.source().is_some());
            if point == Checkpoint::InternalArrowRoster {
                assert_eq!(p.source().unwrap().pending(), None);
                assert!(p.source().unwrap().arrows().is_empty());
                assert!(p.target().is_none());
            } else if point == Checkpoint::ObjectInstances {
                assert!(p.source().unwrap().is_complete());
                assert!(p.target().unwrap().is_complete());
                assert_eq!(p.objects().len(), 3);
            } else {
                assert_eq!(p.objects().len(), 1);
                assert!(p.target().is_some());
            }
            assert!(object_view_transport(Arc::clone(&i), &d, o, n, &mut c).is_err());
            assert_eq!(probes.get(), 1);
        }
    }
}

fn family_law(source: &str, target: &str) -> String {
    L.replace("view family(c: Left.Child, b: Bool): Bool = b;", source)
        .replace("view family(d: Right.Child, q: Bool): Bool = q;", target)
}
#[test]
fn finite_view_family_keeps_each_refuted_or_unknown_point_and_the_operation() {
    let law = family_law(
        "view family(c: Left.Child,b:Bool):Bool=b;",
        "view family(d:Right.Child,q:Bool):Bool=false;",
    );
    let i = inputs(&law, A);
    let r = run(Arc::clone(&i), "p", "family", "p");
    assert_eq!(r.outcome(), &Outcome::Refuted(Failed::Value));
    let f = r.family().unwrap();
    assert!(f.is_complete());
    assert_eq!(f.rows().len(), 2);
    assert_eq!(f.rows()[0].outcome(), &Outcome::Preserved);
    assert_eq!(f.rows()[1].outcome(), &Outcome::Refuted(Failed::Value));
    assert_eq!(f.rows()[1].source().unwrap().wire(), Json::Bool(true));
    assert_eq!(f.rows()[1].target().unwrap().wire(), Json::Bool(false));
    r.operation().recheck(&i, &mut quiet()).unwrap();
    r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
    let law = family_law(
        "view family(c:Left.Child,b:Bool):Bool=if b then c.count=0 else true;",
        "view family(d:Right.Child,q:Bool):Bool=true;",
    );
    let i = inputs(&law, &remove(A, "p-count"));
    let r = run(Arc::clone(&i), "p", "family", "p");
    assert_eq!(r.outcome(), &Outcome::Undetermined);
    let f = r.family().unwrap();
    assert!(f.is_complete());
    assert_eq!(f.rows().len(), 2);
    assert_eq!(f.rows()[0].outcome(), &Outcome::Preserved);
    assert_eq!(f.rows()[1].outcome(), &Outcome::Undetermined);
    assert!(f.rows()[1].source().is_none());
    assert!(f.rows()[1].image().is_none());
    assert_eq!(f.rows()[1].target().unwrap().wire(), Json::Bool(true));
    r.operation().recheck(&i, &mut quiet()).unwrap();
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn finite_view_family_follows_reference_images_instead_of_matching_row_numbers() {
    let law = family_law(
        "view family(c:Left.Child,x:(Left.Child,Bool)):(Left.Child,Bool)=x;",
        "view family(d:Right.Child,y:(Right.Child,Bool)):(Right.Child,Bool)=y;",
    );
    let map = edit(
        A,
        "m-entries",
        "[[[\"v\",\"p\"],[\"v\",\"q\"]],[[\"v\",\"r\"],[\"v\",\"s\"]]]",
        "[[[\"v\",\"p\"],[\"v\",\"s\"]],[[\"v\",\"r\"],[\"v\",\"q\"]]]",
    );
    let i = inputs(&law, &map);
    let r = run(Arc::clone(&i), "p", "family", "p");
    assert_eq!(r.outcome(), &Outcome::Preserved);
    let f = r.family().unwrap();
    assert!(f.is_complete());
    assert_eq!(f.rows().len(), 4);
    assert_eq!(f.parameters()[0].forward(), Some([2, 3, 0, 1].as_slice()));
    assert_eq!(f.parameters()[0].inverse(), Some([2, 3, 0, 1].as_slice()));
    for (row, (source, target, expected_index, flag)) in f.rows().iter().zip([
        ("p", "s", 2, false),
        ("p", "s", 3, true),
        ("r", "q", 0, false),
        ("r", "q", 1, true),
    ]) {
        let value = |id: &str| {
            Json::Arr(vec![
                Json::Arr(vec![Json::str("v"), Json::str(id)]),
                Json::Bool(flag),
            ])
        };
        assert_eq!(row.target_row(), expected_index);
        assert_eq!(row.source().unwrap().wire(), value(source));
        assert_eq!(row.image().unwrap().wire(), value(target));
        assert_eq!(row.target().unwrap().wire(), value(target));
    }
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn finite_view_parameter_collision_is_a_type_condition_with_its_whole_domains() {
    use archsig::construction::maps::FamilyTypeFailure;
    let law = family_law(
        "view family(c:Left.Child,x:Option<Left.Child>):Bool=true;",
        "view family(d:Right.Child,y:Option<Right.Child>):Bool=true;",
    );
    let map = edit(
        A,
        "m-entries",
        "[[\"v\",\"r\"],[\"v\",\"s\"]]",
        "[[\"v\",\"r\"],[\"v\",\"q\"]]",
    );
    let i = inputs(&law, &map);
    let r = run(Arc::clone(&i), "p", "family", "p");
    assert_eq!(
        r.outcome(),
        &Outcome::Refuted(Failed::ParameterType { position: 1 })
    );
    let f = r.family().unwrap();
    assert!(!f.is_complete());
    assert!(f.rows().is_empty());
    let map = &f.parameters()[0];
    assert_eq!(map.source().len(), 3);
    assert_eq!(map.target().len(), 3);
    assert_eq!(map.images().len(), 3);
    assert!(map.forward().is_none());
    assert!(map.inverse().is_none());
    assert!(map.failures().iter().any(
        |f| matches!(f,FamilyTypeFailure::Collision { target: Some(1), sources, image }
                if sources==&[1,2] && image == &map.images()[1])
    ));
    assert!(
        map.failures()
            .iter()
            .any(|f| matches!(f, FamilyTypeFailure::Unreached { target: 2 }))
    );
    r.operation().recheck(&i, &mut quiet()).unwrap();
    r.recheck(i, &mut quiet()).unwrap();
}

fn outside_box_inputs(source: &str, target: &str) -> Arc<CheckedInputs> {
    let extra = r#",{"kind":"data","name":"Left.Box","meaning":"有限値。","constructors":[{"name":"Put","meaning":"参照値。","arguments":[["Ref","Left.Child"]]}]}"#;
    let left = String::from_utf8(D.to_vec()).unwrap();
    assert_eq!(left.matches("  ]}]").count(), 1);
    let left = left.replace("  ]}]", &format!("{extra}\n  ]}}]"));
    let law = family_law(source, target);
    let map = edit(
        A,
        "m-entries",
        "[[\"v\",\"r\"],[\"v\",\"s\"]]",
        "[[\"v\",\"r\"],[\"v\",\"q\"]]",
    );
    inputs_with_left(left.as_bytes(), &law, &map)
}

#[test]
fn finite_view_parameter_retains_the_collision_of_equal_outside_target_images() {
    use archsig::construction::maps::FamilyTypeFailure;
    let i = outside_box_inputs(
        "view family(c:Left.Child,x:Left.Box):Bool=true;",
        "view family(d:Right.Child,y:Left.Box):Bool=true;",
    );
    let r = run(Arc::clone(&i), "p", "family", "p");
    assert_eq!(
        r.outcome(),
        &Outcome::Refuted(Failed::ParameterType { position: 1 })
    );
    let map = &r.family().unwrap().parameters()[0];
    assert_eq!(map.source().len(), 2);
    assert_eq!(map.target().len(), 2);
    assert_eq!(map.images().len(), 2);
    assert_eq!(map.images()[0], map.images()[1]);
    assert_eq!(
        map.images()[0].wire().canonical(),
        "{\"args\":[[\"v\",\"q\"]],\"tag\":\"Put\"}"
    );
    assert!(matches!(map.failures(), [
        FamilyTypeFailure::OutsideTarget { source: 0 },
        FamilyTypeFailure::OutsideTarget { source: 1 },
        FamilyTypeFailure::Collision { target: None, sources, image },
        FamilyTypeFailure::Unreached { target: 0 },
        FamilyTypeFailure::Unreached { target: 1 },
    ] if sources == &[0, 1] && image == &map.images()[0]));
    assert!(map.forward().is_none());
    assert!(map.inverse().is_none());
    r.operation().recheck(&i, &mut quiet()).unwrap();
    r.recheck(i, &mut quiet()).unwrap();
}

#[test]
fn finite_view_return_retains_the_collision_of_equal_outside_target_images() {
    use archsig::construction::maps::{FamilyTypeFailure, ViewFamilyReturnMap};
    let i = outside_box_inputs(
        "view family(c:Left.Child,b:Bool):Option<Left.Box> = none<Left.Box>;",
        "view family(d:Right.Child,q:Bool):Option<Left.Box> = none<Left.Box>;",
    );
    let r = run(Arc::clone(&i), "p", "family", "p");
    assert_eq!(r.outcome(), &Outcome::Refuted(Failed::ValueType));
    let Some(ViewFamilyReturnMap::Finite(map)) = r.family().unwrap().returns() else {
        panic!("{:?}", r.family())
    };
    assert_eq!(map.source().len(), 3);
    assert_eq!(map.target().len(), 3);
    assert_eq!(map.images().len(), 3);
    assert_eq!(map.images()[1], map.images()[2]);
    assert_eq!(map.images()[0].wire().canonical(), "{\"none\":true}");
    assert_eq!(
        map.images()[1].wire().canonical(),
        "{\"some\":{\"args\":[[\"v\",\"q\"]],\"tag\":\"Put\"}}"
    );
    assert!(matches!(map.failures(), [
        FamilyTypeFailure::OutsideTarget { source: 1 },
        FamilyTypeFailure::OutsideTarget { source: 2 },
        FamilyTypeFailure::Collision { target: None, sources, image },
        FamilyTypeFailure::Unreached { target: 1 },
        FamilyTypeFailure::Unreached { target: 2 },
    ] if sources == &[1, 2] && image == &map.images()[1]));
    assert!(map.forward().is_none());
    assert!(map.inverse().is_none());
    assert!(r.family().unwrap().rows().is_empty());
    assert!(!r.family().unwrap().is_complete());
    for e in [r.source().unwrap(), r.target().unwrap()] {
        let ObjectEvaluationOutcome::FiniteView(family) = e.outcome() else {
            panic!("{e:?}")
        };
        assert!(family.is_complete());
        assert_eq!(family.rows().len(), 2);
        for row in family.rows() {
            let wire = row.evaluation().wire();
            let output = f(&arr(f(&wire, "answers"))[0], "outputs");
            let id = f(f(output, "value"), "node");
            let node = arr(f(&wire, "nodes"))
                .iter()
                .find(|node| f(node, "id") == id)
                .unwrap();
            assert_eq!(f(node, "value").canonical(), "{\"none\":true}");
        }
    }
    r.operation().recheck(&i, &mut quiet()).unwrap();
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn finite_view_family_keeps_non_applicability_separate_from_membership_conditions() {
    let i = inputs(L, A);
    let r = run(Arc::clone(&i), "p", "family", "r");
    assert_eq!(r.outcome(), &Outcome::Preserved);
    assert!(r.family().unwrap().rows().is_empty());
    assert!(matches!(
        r.source().unwrap().outcome(),
        ObjectEvaluationOutcome::NotApplicable
    ));
    assert!(matches!(
        r.target().unwrap().outcome(),
        ObjectEvaluationOutcome::NotApplicable
    ));
    let law = family_law(
        "view family(c:Left.Child,a:Left.ExternalRoot,e:Left.ExternalChild[a],b:Bool):Bool=b;",
        "view family(d:Right.Child,z:Left.ExternalRoot,w:Left.ExternalChild[z],q:Bool):Bool=q;",
    );
    let i = inputs(&law, A);
    let r = run(Arc::clone(&i), "p", "family", "p");
    assert_eq!(r.outcome(), &Outcome::Undetermined);
    assert!(!r.family().unwrap().is_complete());
    assert!(matches!(
        r.source().unwrap().outcome(),
        ObjectEvaluationOutcome::Conditional(_)
    ));
    assert!(matches!(
        r.target().unwrap().outcome(),
        ObjectEvaluationOutcome::Conditional(_)
    ));
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn finite_view_family_uses_fixed_owner_fibers_and_retains_needed_owner_slots() {
    let law = family_law(
        "view family(c:Left.Root,x:(Left.Child[c],Bool)):Bool=true;",
        "view family(d:Right.Root,y:(Right.Child[d],Bool)):Bool=true;",
    );
    let i = inputs(&law, A);
    let r = run(Arc::clone(&i), "a", "family", "a");
    assert_eq!(r.outcome(), &Outcome::Preserved);
    assert_eq!(r.family().unwrap().rows().len(), 4);
    assert_eq!(r.family().unwrap().parameters()[0].source().len(), 4);
    r.recheck(i, &mut quiet()).unwrap();
    let law = family_law(
        "view family(c:Left.Child,a:Left.ExternalRoot,x:Option<Left.ExternalChild[a]>):Bool=true;",
        "view family(d:Right.Child,z:Left.ExternalRoot,y:Option<Left.ExternalChild[z]>):Bool=true;",
    );
    let i = inputs(&law, A);
    let r = run(Arc::clone(&i), "p", "family", "p");
    assert_eq!(r.outcome(), &Outcome::Undetermined);
    let f = r.family().unwrap();
    assert!(!f.is_complete());
    assert!(f.rows().is_empty());
    assert!(f.parameters()[0].missing().iter().any(
        |fact| fact.subject == "y" && fact.field.as_deref() == Some("Left.ExternalChild.owner")
    ));
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn finite_view_family_distinguishes_empty_domain_from_the_single_empty_list() {
    let map = A
        .lines()
        .filter(|line| !line.contains("\"id\":\"y\""))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]");
    for (ty, body, rows) in [
        ("(Left.ExternalChild,Bool)", "true", 0),
        ("List<Left.ExternalChild>", "true", 1),
    ] {
        let law = family_law(
            &format!("view family(c:Left.Child,x:{ty}):Bool={body};"),
            &format!("view family(d:Right.Child,y:{ty}):Bool={body};"),
        );
        let i = inputs(&law, &map);
        let r = run(Arc::clone(&i), "p", "family", "p");
        assert_eq!(r.outcome(), &Outcome::Preserved);
        let f = r.family().unwrap();
        assert!(f.is_complete());
        assert_eq!(f.rows().len(), rows);
        r.recheck(i, &mut quiet()).unwrap();
    }
    let law = family_law(
        "view family(c:Left.Child,x:List<Left.ExternalChild>):List<Left.ExternalChild> =x;",
        "view family(d:Right.Child,y:List<Left.ExternalChild>):List<Left.ExternalChild> =y;",
    );
    let i = inputs(&law, &map);
    let r = run(Arc::clone(&i), "p", "family", "p");
    assert_eq!(r.outcome(), &Outcome::Preserved);
    let f = r.family().unwrap();
    assert_eq!(f.rows().len(), 1);
    assert_eq!(f.rows()[0].target().unwrap().wire(), Json::Arr(vec![]));
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn finite_view_family_keeps_all_data_option_set_and_boolean_product_values() {
    let extra = r#",{"kind":"data","name":"Left.Choice","meaning":"有限和。","constructors":[{"name":"No","meaning":"引数なし。","arguments":[]},{"name":"Yes","meaning":"Boolを保持。","arguments":["Bool"]}]}"#;
    let left = String::from_utf8(D.to_vec())
        .unwrap()
        .replace("  ]}]", &format!("{extra}\n  ]}}]"));
    let law = family_law(
        "view family(c:Left.Child,x:Left.Choice,b:(Set<Bool>,Option<Bool>)):(Left.Choice,(Set<Bool>,Option<Bool>))=(x,b);",
        "view family(d:Right.Child,u:Left.Choice,v:(Set<Bool>,Option<Bool>)):(Left.Choice,(Set<Bool>,Option<Bool>))=(u,v);",
    );
    let i = inputs_with_left(left.as_bytes(), &law, A);
    let r = run(Arc::clone(&i), "p", "family", "p");
    assert_eq!(r.outcome(), &Outcome::Preserved);
    let f = r.family().unwrap();
    assert!(f.is_complete());
    assert_eq!(f.rows().len(), 36);
    let mut expected = Vec::new();
    for choice in [
        Json::obj([("tag", Json::str("No")), ("args", Json::Arr(vec![]))]),
        Json::obj([
            ("tag", Json::str("Yes")),
            ("args", Json::Arr(vec![Json::Bool(false)])),
        ]),
        Json::obj([
            ("tag", Json::str("Yes")),
            ("args", Json::Arr(vec![Json::Bool(true)])),
        ]),
    ] {
        for set in [
            vec![],
            vec![Json::Bool(false)],
            vec![Json::Bool(true)],
            vec![Json::Bool(false), Json::Bool(true)],
        ] {
            for option in [
                Json::obj([("none", Json::Bool(true))]),
                Json::obj([("some", Json::Bool(false))]),
                Json::obj([("some", Json::Bool(true))]),
            ] {
                expected.push(Json::Arr(vec![
                    choice.clone(),
                    Json::Arr(vec![Json::Arr(set.clone()), option]),
                ]));
            }
        }
    }
    assert_eq!(
        f.rows()
            .iter()
            .map(|r| r.source().unwrap().wire())
            .collect::<Vec<_>>(),
        expected
    );
    for row in f.rows() {
        assert_eq!(row.source().unwrap().wire(), row.target().unwrap().wire());
        assert_eq!(row.outcome(), &Outcome::Preserved);
    }
    r.recheck(i, &mut quiet()).unwrap();
}

#[test]
fn finite_view_family_preserves_numeric_product_return_maps_without_sampling_the_type() {
    use archsig::construction::maps::ViewFamilyReturnMap;
    let law = family_law(
        "view family(c:Left.Child,b:Bool):(Z,Q)=(if b then c.count+1 else c.count,rat(1,2));",
        "view family(d:Right.Child,q:Bool):(Z,Q)=(if q then 3 else 2,rat(1,2));",
    );
    let i = inputs(&law, A);
    let r = run(Arc::clone(&i), "p", "family", "p");
    assert_eq!(r.outcome(), &Outcome::Preserved);
    let f = r.family().unwrap();
    assert!(matches!(f.returns(), Some(ViewFamilyReturnMap::Numeric(_))));
    for (row, n) in f.rows().iter().zip(["2", "3"]) {
        let expected = Json::Arr(vec![
            Json::str(n),
            Json::Arr(vec![Json::str("1"), Json::str("2")]),
        ]);
        assert_eq!(row.source().unwrap().wire(), expected);
        assert_eq!(row.image().unwrap().wire(), expected);
        assert_eq!(row.target().unwrap().wire(), expected);
    }
    r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
    let r = run(Arc::clone(&i), "r", "family", "r");
    assert_eq!(r.outcome(), &Outcome::Refuted(Failed::Value));
    assert_eq!(r.family().unwrap().rows().len(), 2);
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn finite_view_family_moves_owned_container_types_with_the_original_owner_parameter_names() {
    let law = family_law(
        "view family(c:Left.Root,x:Set<Left.Child[c]>):Bool=true;",
        "view family(d:Right.Root,y:Set<Right.Child[d]>):Bool=true;",
    );
    let i = inputs(&law, A);
    let r = run(Arc::clone(&i), "a", "family", "a");
    assert_eq!(r.outcome(), &Outcome::Preserved);
    let f = r.family().unwrap();
    assert_eq!(f.rows().len(), 4);
    let map = &f.parameters()[0];
    assert_eq!(map.forward(), Some([0, 1, 2, 3].as_slice()));
    assert_eq!(map.source_parameter().name, "x");
    assert_eq!(map.target_parameter().name, "y");
    assert_eq!(
        map.source_type(),
        &archsig::types::Type::Set(Box::new(archsig::types::Type::Owned(
            "Left.Child".into(),
            "c".into()
        )))
    );
    assert_eq!(
        map.target_type(),
        &archsig::types::Type::Set(Box::new(archsig::types::Type::Owned(
            "Right.Child".into(),
            "d".into()
        )))
    );
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn finite_view_family_recheck_rejects_changed_input_bytes_body_and_unused_provenance() {
    let i = inputs(L, A);
    let r = run(Arc::clone(&i), "p", "family", "p");
    for changed in [
        inputs(&L.replace("Bool = q;", "Bool = not q;"), A),
        inputs(L, &edit(A, "p-count", "\"2\"", "\"9\"")),
        inputs(L, &A.replace("amount-r1", "amount-r2")),
    ] {
        assert!(r.recheck(changed, &mut quiet()).is_err());
    }
    r.recheck(i, &mut quiet()).unwrap();
}

#[test]
fn finite_view_parameter_outside_target_is_rejected_even_for_two_absent_axes() {
    use archsig::construction::maps::FamilyTypeFailure;
    let law = family_law(
        "view family(c:Left.Child,x:Option<Left.Child>):Bool=true;",
        "view family(d:Right.Child,y:Option<Right.Child>):Bool=true;",
    );
    let map=A.replace("{\"id\":\"m\",\"type\":\"Bridge.Move\",\"origin\":\"model\"},", "{\"id\":\"a2\",\"type\":\"Left.Root\",\"origin\":\"model\"},{\"id\":\"t\",\"type\":\"Left.Child\",\"origin\":\"model\"},{\"id\":\"m\",\"type\":\"Bridge.Move\",\"origin\":\"model\"},")
        .replace("{\"id\":\"m-from\"", "{\"id\":\"t-owner\",\"subject\":\"t\",\"field\":\"Left.Child.owner\",\"value\":[\"v\",\"a2\"],\"origin\":\"model\"},{\"id\":\"m-from\"");
    let i = inputs(&law, &map);
    for subject in ["p", "r"] {
        let r = run(Arc::clone(&i), "p", "family", subject);
        assert_eq!(
            r.outcome(),
            &Outcome::Refuted(Failed::ParameterType { position: 1 })
        );
        let f = r.family().unwrap();
        let map = &f.parameters()[0];
        assert_eq!(map.source().len(), 4);
        assert_eq!(map.target().len(), 3);
        assert!(
            map.failures()
                .contains(&FamilyTypeFailure::OutsideTarget { source: 3 })
        );
        if subject == "r" {
            assert!(matches!(
                r.source().unwrap().outcome(),
                ObjectEvaluationOutcome::NotApplicable
            ));
            assert!(matches!(
                r.target().unwrap().outcome(),
                ObjectEvaluationOutcome::NotApplicable
            ));
        }
        r.operation().recheck(&i, &mut quiet()).unwrap();
        r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
    }
}

#[test]
fn unsupported_family_return_transport_keeps_the_already_computed_view_values() {
    let law = family_law(
        "view family(c:Left.Child,b:Bool):List<(Z,Left.Child)> = list<(Z,Left.Child)>[(if b then c.count+1 else c.count,c)];",
        "view family(d:Right.Child,q:Bool):List<(Z,Right.Child)> = list<(Z,Right.Child)>[(if q then 3 else 2,d)];",
    );
    let i = inputs(&law, A);
    let d = declarations(&i);
    let (o, n) = indices(&i, "p", "family", "p");
    let Err(Error::NotImplemented {
        operation,
        returns,
        partial: Some(p),
        ..
    }) = object_view_transport(Arc::clone(&i), &d, o, n, &mut quiet())
    else {
        panic!("unsupported type transport");
    };
    assert_eq!(
        returns,
        archsig::types::Type::List(Box::new(archsig::types::Type::Tuple(vec![
            archsig::types::Type::Z,
            archsig::types::Type::Ref("Left.Child".into()),
        ])))
    );
    assert!(p.outcome().is_none());
    assert!(!p.family().unwrap().is_complete());
    assert!(p.family().unwrap().rows().is_empty());
    assert_eq!(
        p.family().unwrap().parameters()[0].forward(),
        Some([0, 1].as_slice())
    );
    for evaluation in [p.source().unwrap(), p.target().unwrap()] {
        let ObjectEvaluationOutcome::FiniteView(family) = evaluation.outcome() else {
            panic!("retained finite family");
        };
        assert!(family.is_complete());
        assert_eq!(family.rows().len(), 2);
        for (row, expected) in family.rows().iter().zip(["2", "3"]) {
            let wire = row.evaluation().wire();
            let output = f(&arr(f(&wire, "answers"))[0], "outputs");
            let id = f(f(output, "value"), "node");
            let node = arr(f(&wire, "nodes"))
                .iter()
                .find(|node| f(node, "id") == id)
                .unwrap();
            let items = arr(f(node, "value"));
            assert_eq!(items.len(), 1);
            let pair = arr(&items[0]);
            assert_eq!(pair.len(), 2);
            assert_eq!(pair[0], Json::str(expected));
            assert_eq!(arr(&pair[1])[0], Json::str("v"));
        }
    }
    operation.recheck(&i, &mut quiet()).unwrap();
}

#[test]
fn mixed_primitive_products_keep_whole_type_identity_for_closed_and_finite_views() {
    use archsig::construction::maps::ViewFamilyReturnMap;
    for parameter in [false, true] {
        let law = if parameter {
            family_law(
                "view family(c:Left.Child,b:Bool):(Bool,(Z,Q))=(b,(if b then c.count+1 else c.count,rat(1,2)));",
                "view family(d:Right.Child,q:Bool):(Bool,(Z,Q))=(q,(if q then 3 else 2,rat(1,2)));",
            )
        } else {
            family_law(
                "view family(c:Left.Child):(Bool,(Z,Q))=(true,(c.count,rat(1,2)));",
                "view family(d:Right.Child):(Bool,(Z,Q))=(true,(2,rat(1,2)));",
            )
        };
        let i = inputs(&law, A);
        let r = run(Arc::clone(&i), "p", "family", "p");
        assert_eq!(r.outcome(), &Outcome::Preserved);
        if parameter {
            let f = r.family().unwrap();
            assert!(matches!(
                f.returns(),
                Some(ViewFamilyReturnMap::PrimitiveIdentity(_))
            ));
            assert!(f.is_complete());
            assert_eq!(f.rows().len(), 2);
            for (row, (b, n)) in f.rows().iter().zip([(false, "2"), (true, "3")]) {
                let expected = Json::Arr(vec![
                    Json::Bool(b),
                    Json::Arr(vec![
                        Json::str(n),
                        Json::Arr(vec![Json::str("1"), Json::str("2")]),
                    ]),
                ]);
                assert_eq!(row.source().unwrap().wire(), expected);
                assert_eq!(row.image().unwrap().wire(), expected);
                assert_eq!(row.target().unwrap().wire(), expected);
            }
        } else {
            let Some(ViewValueEquivalence::PrimitiveIdentity(identity)) = r.equivalence() else {
                panic!("mixed product identity missing")
            };
            assert_eq!(
                Some(identity.ty()),
                r.instance().declaration().returns.as_ref()
            );
        }
        r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
        let changed = run(Arc::clone(&i), "r", "family", "r");
        assert_eq!(changed.outcome(), &Outcome::Refuted(Failed::Value));
        changed.recheck(i, &mut quiet()).unwrap();
    }
}

#[test]
fn primitive_containers_preserve_known_empty_values_without_filling_missing_values() {
    use archsig::construction::maps::ViewFamilyReturnMap;
    for parameter in [false, true] {
        let (sp, tp, sc, tc) = if parameter {
            (",b:Bool", ",q:Bool", "b", "q")
        } else {
            ("", "", "true", "true")
        };
        let law = family_law(
            &format!(
                r#"view family(c:Left.Child{sp}):(List<Z>,Option<Q>,Set<Z>,Text,Unit)=(if {sc} then list<Z>[c.count,c.count+1] else list<Z>[],if {sc} then some(rat(1,2)) else none<Q>,if {sc} then set<Z>{{c.count,c.count}} else set<Z>{{}},if {sc} then "known" else "empty",unit);"#
            ),
            &format!(
                r#"view family(d:Right.Child{tp}):(List<Z>,Option<Q>,Set<Z>,Text,Unit)=(if {tc} then list<Z>[2,3] else list<Z>[],if {tc} then some(rat(1,2)) else none<Q>,if {tc} then set<Z>{{2}} else set<Z>{{}},if {tc} then "known" else "empty",unit);"#
            ),
        );
        let expected = |present| {
            Json::Arr(if present {
                vec![
                    Json::Arr(vec![Json::str("2"), Json::str("3")]),
                    Json::obj([("some", Json::Arr(vec![Json::str("1"), Json::str("2")]))]),
                    Json::Arr(vec![Json::str("2")]),
                    Json::str("known"),
                    Json::Arr(vec![]),
                ]
            } else {
                vec![
                    Json::Arr(vec![]),
                    Json::obj([("none", Json::Bool(true))]),
                    Json::Arr(vec![]),
                    Json::str("empty"),
                    Json::Arr(vec![]),
                ]
            })
        };
        let i = inputs(&law, A);
        let r = run(Arc::clone(&i), "p", "family", "p");
        assert_eq!(r.outcome(), &Outcome::Preserved);
        if parameter {
            let f = r.family().unwrap();
            assert!(matches!(
                f.returns(),
                Some(ViewFamilyReturnMap::PrimitiveIdentity(_))
            ));
            assert!(f.is_complete());
            assert_eq!(f.rows().len(), 2);
            for (row, present) in f.rows().iter().zip([false, true]) {
                assert_eq!(row.source().unwrap().wire(), expected(present));
                assert_eq!(row.image().unwrap().wire(), expected(present));
                assert_eq!(row.target().unwrap().wire(), expected(present));
            }
        } else {
            assert!(matches!(
                r.equivalence(),
                Some(ViewValueEquivalence::PrimitiveIdentity(_))
            ));
            assert_eq!(r.source_value().unwrap().wire(), expected(true));
            assert_eq!(r.image().unwrap().wire(), expected(true));
            assert_eq!(r.target_value().unwrap().wire(), expected(true));
        }
        r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
        let changed = run(Arc::clone(&i), "r", "family", "r");
        assert_eq!(changed.outcome(), &Outcome::Refuted(Failed::Value));
        changed.recheck(i, &mut quiet()).unwrap();
        let i = inputs(&law, &remove(A, "p-count"));
        let missing = run(Arc::clone(&i), "p", "family", "p");
        assert_eq!(missing.outcome(), &Outcome::Undetermined);
        if parameter {
            let rows = missing.family().unwrap().rows();
            assert_eq!(rows[0].outcome(), &Outcome::Preserved);
            assert_eq!(rows[0].source().unwrap().wire(), expected(false));
            assert_eq!(rows[1].outcome(), &Outcome::Undetermined);
            assert!(rows[1].source().is_none());
            assert!(rows[1].image().is_none());
            assert_eq!(rows[1].target().unwrap().wire(), expected(true));
        } else {
            assert!(missing.source_value().is_none());
            assert!(missing.image().is_none());
        }
        missing.operation().recheck(&i, &mut quiet()).unwrap();
        missing.recheck(i, &mut quiet()).unwrap();
    }
}
