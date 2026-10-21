use archsig::{
    canonical::Json,
    construction::{
        ConstructionFailure, construct,
        maps::{
            DeclarationCorrespondence, LawApplication, LawConditionFailure as Failed,
            LawTransportOutcome as Outcome, ObjectLawTransport, ObjectLawTransportFailure as Error,
            correspondence, declaration_correspondence, object_law_transport,
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
const D: &[u8] = include_bytes!("fixtures/object-law-transport.atoms.json");
const L: &str = include_str!("fixtures/object-law-transport.law");
const A: &str = include_str!("fixtures/object-view-transport.archmap.json");
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn inputs(law: &str, map: &str) -> Arc<CheckedInputs> {
    let right = include_bytes!("fixtures/object-law-transport-right.atoms.json");
    let defs = archsig::definition::check_definitions(&[("left", D), ("right", right)]).unwrap();
    let ld = &defs.vocabularies["Left"].digest;
    let rd = &defs.vocabularies["Right"].digest;
    let bridge = include_str!("fixtures/object-law-transport-bridge.atoms.json")
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
fn run(i: Arc<CheckedInputs>, object: &str, view: &str, subject: &str) -> ObjectLawTransport {
    let d = declarations(&i);
    let (o, r) = indices(&i, object, view, subject);
    object_law_transport(i, &d, o, r, &mut quiet()).unwrap()
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
fn actual_truth_and_required_status_are_preserved_separately_from_lawfulness() {
    let i = inputs(L, A);
    for (name, truth, required) in [
        ("bounded", true, true),
        ("no", false, true),
        ("advisory", false, false),
    ] {
        let r = run(Arc::clone(&i), "p", name, "p");
        assert_eq!(r.outcome(), &Outcome::Preserved);
        for reading in [r.source_reading().unwrap(), r.target_reading().unwrap()] {
            assert_eq!(reading.required(), required);
            assert_eq!(reading.application(), &LawApplication::Guard(Some(true)));
            assert_eq!(reading.body(), Some(truth));
            assert_eq!(reading.conditional(), Some(truth));
        }
        for e in [r.source().unwrap(), r.target().unwrap()] {
            let ObjectEvaluationOutcome::Evaluated(e) = e.outcome() else {
                panic!()
            };
            assert!(Arc::ptr_eq(&i, &e.prepared().shared_inputs()));
            assert_eq!(
                f(&arr(f(&e.wire(), "answers"))[0], "status"),
                &Json::str(if truth { "established" } else { "refuted" })
            );
        }
        r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
    }
    let r = run(Arc::clone(&i), "p", "role", "p");
    assert_eq!(
        r.outcome(),
        &Outcome::Refuted(Failed::RequiredStatus {
            source: true,
            target: false
        })
    );
    assert!(r.source().is_none());
    r.operation().recheck(&i, &mut quiet()).unwrap();
}

#[test]
fn guard_and_body_mismatches_keep_the_original_evaluation_and_operation() {
    let i = inputs(L, A);
    let r = run(Arc::clone(&i), "r", "bounded", "r");
    assert_eq!(r.outcome(), &Outcome::Refuted(Failed::Holds));
    assert_eq!(r.source_reading().unwrap().body(), Some(false));
    assert_eq!(r.target_reading().unwrap().body(), Some(true));
    let r = run(Arc::clone(&i), "r", "guarded", "r");
    assert_eq!(r.outcome(), &Outcome::Refuted(Failed::Applicability));
    assert_eq!(
        r.source_reading().unwrap().application(),
        &LawApplication::Guard(Some(false))
    );
    assert_eq!(r.source_reading().unwrap().conditional(), Some(true));
    assert_eq!(
        r.target_reading().unwrap().application(),
        &LawApplication::Guard(Some(true))
    );
    assert_eq!(r.target_reading().unwrap().conditional(), Some(false));
    r.operation().recheck(&i, &mut quiet()).unwrap();
    r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
    let r = run(Arc::clone(&i), "p", "vacuous", "p");
    assert_eq!(r.outcome(), &Outcome::Preserved);
    assert_eq!(r.source_reading().unwrap().body(), Some(false));
    assert_eq!(r.target_reading().unwrap().body(), Some(true));
    for r in [r.source_reading().unwrap(), r.target_reading().unwrap()] {
        assert_eq!(r.application(), &LawApplication::Guard(Some(false)));
        assert_eq!(r.conditional(), Some(true));
    }
}

#[test]
fn quantified_bodies_use_the_whole_law_truth_instead_of_a_symbolic_point_value() {
    let i = inputs(L, A);
    for (name, value) in [("whole", false), ("nested", true)] {
        let r = run(Arc::clone(&i), "p", name, "p");
        assert_eq!(r.outcome(), &Outcome::Preserved);
        for v in [r.source_reading().unwrap(), r.target_reading().unwrap()] {
            assert_eq!(v.application(), &LawApplication::Guard(Some(true)));
            assert_eq!(v.body(), Some(value));
            assert_eq!(v.conditional(), Some(value));
        }
        r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
    }
}

#[test]
fn missing_guard_body_and_object_membership_are_distinct_and_not_false() {
    let i = inputs(L, &remove(A, "p-count"));
    let r = run(Arc::clone(&i), "p", "bounded", "p");
    assert_eq!(r.outcome(), &Outcome::Undetermined);
    assert_eq!(
        r.source_reading().unwrap().application(),
        &LawApplication::Guard(Some(true))
    );
    assert_eq!(r.source_reading().unwrap().body(), None);
    assert_eq!(r.target_reading().unwrap().body(), Some(true));
    let r = run(Arc::clone(&i), "p", "unknownGuard", "p");
    assert_eq!(r.outcome(), &Outcome::Undetermined);
    assert_eq!(
        r.source_reading().unwrap().application(),
        &LawApplication::Guard(None)
    );
    assert_eq!(r.source_reading().unwrap().body(), Some(true));
    assert_eq!(r.source_reading().unwrap().conditional(), Some(true));
    let r = run(Arc::clone(&i), "p", "conditional", "p");
    assert_eq!(r.outcome(), &Outcome::Undetermined);
    let LawApplication::ConditionalMembership(conditions) =
        r.source_reading().unwrap().application()
    else {
        panic!()
    };
    assert!(conditions.iter().any(|c| c.slot().subject == "y"
        && c.slot().field.as_deref() == Some("Left.ExternalChild.owner")));
    let r = run(Arc::clone(&i), "p", "bounded", "r");
    assert_eq!(r.outcome(), &Outcome::Preserved);
    assert_eq!(
        r.source_reading().unwrap().application(),
        &LawApplication::OutsideObject
    );
    assert_eq!(
        r.target_reading().unwrap().application(),
        &LawApplication::OutsideObject
    );
    assert_eq!(r.source_reading().unwrap().body(), None);
}

#[test]
fn finite_completions_keep_original_guard_and_body_separate_from_the_implication() {
    let i = inputs(L, A);
    for name in ["finiteGuard", "finiteBody", "finiteWhole"] {
        let r = run(Arc::clone(&i), "p", name, "p");
        assert_eq!(r.outcome(), &Outcome::Undetermined);
        let source = r.source_reading().unwrap();
        assert_eq!(source.application(), &LawApplication::Guard(None));
        assert_eq!(source.body(), None);
        assert_eq!(source.conditional(), Some(true));
        let target = r.target_reading().unwrap();
        assert_eq!(target.application(), &LawApplication::Guard(Some(true)));
        assert_eq!(target.body(), Some(true));
        r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
        let ObjectEvaluationOutcome::Evaluated(e) = r.source().unwrap().outcome() else {
            panic!()
        };
        let wire = e.wire().canonical();
        assert!(wire.contains("all_completions"));
        assert!(wire.contains("not_applicable"));
        assert!(wire.contains("Left.Child.flag"));
    }
    let r = run(Arc::clone(&i), "p", "falseGuard", "p");
    assert_eq!(r.outcome(), &Outcome::Refuted(Failed::Applicability));
    let source = r.source_reading().unwrap();
    assert_eq!(source.application(), &LawApplication::Guard(Some(false)));
    assert_eq!(source.body(), None);
    assert_eq!(source.conditional(), Some(true));
    r.operation().recheck(&i, &mut quiet()).unwrap();
    for name in ["falseBoth", "finiteRead"] {
        let r = run(Arc::clone(&i), "p", name, "p");
        assert_eq!(r.outcome(), &Outcome::Preserved);
        r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
    }
}

#[test]
fn finite_owner_completions_do_not_turn_a_false_or_unknown_guard_into_true() {
    let map = A.replace(
        "\"subjects\":[",
        "\"subjects\":[\n{\"id\":\"z\",\"type\":\"Left.ExternalRoot\",\"origin\":\"model\"},",
    );
    let i = inputs(L, &map);
    let r = run(Arc::clone(&i), "p", "refGuard", "p");
    assert_eq!(r.outcome(), &Outcome::Undetermined);
    assert_eq!(
        r.source_reading().unwrap().application(),
        &LawApplication::Guard(None)
    );
    assert_eq!(r.source_reading().unwrap().conditional(), Some(true));
    assert!(
        r.instance()
            .bindings()
            .iter()
            .any(|b| b.parameter().name == "x" && b.subject().subject == "x")
    );
    assert!(
        r.instance()
            .bindings()
            .iter()
            .any(|b| b.parameter().name == "e" && b.subject().subject == "y")
    );
    r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
    let r = run(Arc::clone(&i), "p", "falseRef", "p");
    assert_eq!(r.outcome(), &Outcome::Refuted(Failed::Applicability));
    assert_eq!(
        r.source_reading().unwrap().application(),
        &LawApplication::Guard(Some(false))
    );
    assert_eq!(r.source_reading().unwrap().body(), None);
    assert_eq!(r.source_reading().unwrap().conditional(), Some(true));
    r.operation().recheck(&i, &mut quiet()).unwrap();
    r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
}

#[test]
fn stopped_completion_reading_keeps_the_complete_source_dag_without_a_partial_guard() {
    let i = inputs(L, A);
    let d = declarations(&i);
    let (o, n) = indices(&i, "p", "finiteGuard", "p");
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let normal = object_law_transport(
        Arc::clone(&i),
        &d,
        o,
        n,
        &mut Control::new(Limits::default(), move |p| {
            if p == Checkpoint::ObjectLawTransport {
                seen.set(seen.get() + 1);
            }
            Usage::default()
        }),
    )
    .unwrap();
    let total = count.get();
    assert!(total >= 8);
    // 両補完caseの読取り。後続はsource後・target後・比較後の三checkpoint。
    for at in [total - 4, total - 3] {
        for mode in 0..4 {
            let count = Rc::new(Cell::new(0));
            let seen = count.clone();
            let mut c = Control::new(
                Limits {
                    time_ms: Some(1),
                    memory_mib: Some(1),
                },
                move |p| {
                    if p == Checkpoint::ObjectLawTransport {
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
            let Error::Stopped {
                reason,
                operation,
                partial: Some(p),
                ..
            } = object_law_transport(Arc::clone(&i), &d, o, n, &mut c).unwrap_err()
            else {
                panic!()
            };
            assert_eq!(reason, c.stop_reason().unwrap());
            operation.recheck(&i, &mut quiet()).unwrap();
            let ObjectEvaluationOutcome::Evaluated(e) = p.source().unwrap().outcome() else {
                panic!()
            };
            let ObjectEvaluationOutcome::Evaluated(original) = normal.source().unwrap().outcome()
            else {
                panic!()
            };
            assert_eq!(e.wire(), original.wire());
            assert!(p.source_reading().is_none());
            assert!(p.target().is_none());
            assert!(p.target_reading().is_none());
            assert!(p.outcome().is_none());
            assert_eq!(count.get(), at);
            assert!(matches!(
                object_law_transport(Arc::clone(&i), &d, o, n, &mut c),
                Err(Error::Construction(ConstructionFailure::Stopped(_)))
            ));
            assert_eq!(count.get(), at);
        }
    }
}

#[test]
fn fixed_external_reference_bindings_and_original_support_are_retained() {
    let i = inputs(L, A);
    let r = run(Arc::clone(&i), "p", "external", "p");
    assert_eq!(r.outcome(), &Outcome::Preserved);
    assert!(
        r.target_instance()
            .unwrap()
            .bindings()
            .iter()
            .any(|b| b.parameter().name == "z" && b.subject().subject == "m")
    );
    let r = run(Arc::clone(&i), "p", "bounded", "p");
    let ObjectEvaluationOutcome::Evaluated(e) = r.source().unwrap().outcome() else {
        panic!()
    };
    let wire = e.wire();
    let answer = &arr(f(&wire, "answers"))[0];
    let root = f(f(f(answer, "outputs"), "evaluation"), "node");
    let evaluated = arr(f(&wire, "nodes"))
        .iter()
        .find(|n| f(n, "id") == root)
        .unwrap();
    assert!(
        arr(f(evaluated, "support"))
            .iter()
            .any(|s| s.canonical().contains("p-count"))
    );
    let body = r
        .instance()
        .declaration()
        .expressions
        .iter()
        .find(|e| e.kind == archsig::law::model::ExpressionKind::Body)
        .unwrap()
        .span;
    assert_eq!(
        &r.source_readings().source_law().bytes()[body.0..body.1],
        b"c.count = 2"
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
fn incomplete_signatures_and_infinite_families_are_not_used_as_pointwise_evidence() {
    let changed = L.replace("law required bounded(d:", "law required other(d:");
    let i = inputs(&changed, A);
    let r = run(Arc::clone(&i), "p", "bounded", "p");
    assert!(matches!(
        r.outcome(),
        Outcome::Refuted(Failed::Declaration { .. })
    ));
    r.operation().recheck(&i, &mut quiet()).unwrap();
    let infinite = L
        .replace("b: Bool): b", "b: Z): b = 0")
        .replace("q: Bool): q", "q: Z): q = 0");
    let i = inputs(&infinite, A);
    let d = declarations(&i);
    let (o, n) = indices(&i, "p", "family", "p");
    let Error::NotImplemented {
        operation,
        object,
        instance,
    } = object_law_transport(Arc::clone(&i), &d, o, n, &mut quiet()).unwrap_err()
    else {
        panic!()
    };
    assert_eq!(object.subject().subject, "p");
    assert_eq!(instance.parameters().len(), 1);
    assert_eq!(instance.parameters()[0].name, "b");
    operation.recheck(&i, &mut quiet()).unwrap();
    for (o, n) in [(usize::MAX, n), (o, usize::MAX)] {
        assert!(matches!(
            object_law_transport(Arc::clone(&i), &d, o, n, &mut quiet()),
            Err(Error::Construction(ConstructionFailure::InvalidSelection(
                _
            )))
        ));
    }
}

#[test]
fn changes_to_current_role_guard_body_quantity_and_mapping_are_rechecked() {
    let i = inputs(L, A);
    let r = run(Arc::clone(&i), "p", "bounded", "p");
    for changed in [
        inputs(
            &L.replace("law required bounded(d:", "law optional bounded(d:"),
            A,
        ),
        inputs(
            &L.replace(
                "law required bounded(d: Right.Child): 2 = 2",
                "law required bounded(d: Right.Child) when false: 2 = 2",
            ),
            A,
        ),
        inputs(
            &L.replace(
                "law required bounded(d: Right.Child): 2 = 2",
                "law required bounded(d: Right.Child): 2 = 3",
            ),
            A,
        ),
        inputs(L, &edit(A, "p-count", "\"value\":\"2\"", "\"value\":\"4\"")),
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
}

#[test]
fn stopping_inside_target_expression_keeps_completed_source_and_partial_target() {
    let i = inputs(L, A);
    let d = declarations(&i);
    let (o, n) = indices(&i, "p", "bounded", "p");
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let normal = object_law_transport(
        Arc::clone(&i),
        &d,
        o,
        n,
        &mut Control::new(Limits::default(), move |p| {
            if p == Checkpoint::ObjectLawTransport {
                seen.set(seen.get() + 1);
            }
            Usage::default()
        }),
    )
    .unwrap();
    let source_done = count.get() - 2;
    for mode in 0..4 {
        let phase = Rc::new(Cell::new(0));
        let seen = phase.clone();
        let mut c = Control::new(
            Limits {
                time_ms: Some(1),
                memory_mib: Some(1),
            },
            move |p| {
                if p == Checkpoint::ObjectLawTransport {
                    seen.set(seen.get() + 1);
                }
                let stop = p == Checkpoint::Expression && seen.get() >= source_done;
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
            partial: Some(p),
            ..
        } = object_law_transport(Arc::clone(&i), &d, o, n, &mut c).unwrap_err()
        else {
            panic!()
        };
        assert_eq!(reason, c.stop_reason().unwrap());
        operation.recheck(&i, &mut quiet()).unwrap();
        let ObjectEvaluationOutcome::Evaluated(e) = p.source().unwrap().outcome() else {
            panic!()
        };
        let ObjectEvaluationOutcome::Evaluated(original) = normal.source().unwrap().outcome()
        else {
            panic!()
        };
        assert_eq!(e.wire(), original.wire());
        assert_eq!(p.source_reading(), normal.source_reading());
        let ObjectEvaluationOutcome::Evaluated(e) = p.target().unwrap().outcome() else {
            panic!()
        };
        assert_eq!(e.status(), "interrupted");
        assert!(p.target_reading().is_none());
        assert!(p.outcome().is_none());
        assert_eq!(phase.get(), source_done);
    }
}

#[test]
fn fixed_transport_checkpoints_latch_time_memory_and_cancellation() {
    let i = inputs(L, A);
    let d = declarations(&i);
    let (o, n) = indices(&i, "p", "bounded", "p");
    for point in [
        Checkpoint::ObjectLawTransport,
        Checkpoint::ObjectEvaluation,
        Checkpoint::Expression,
    ] {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        object_law_transport(
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
                let failure = object_law_transport(Arc::clone(&i), &d, o, n, &mut c).unwrap_err();
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
                    object_law_transport(Arc::clone(&i), &d, o, n, &mut c),
                    Err(Error::Construction(ConstructionFailure::Stopped(_)))
                ));
                assert_eq!(count.get(), at);
            }
        }
    }
}

#[test]
fn stopped_law_transport_retains_completed_dags_truth_and_only_completed_decisions() {
    let i = inputs(L, A);
    let d = declarations(&i);
    for (subject, expected) in [
        ("p", Outcome::Preserved),
        ("r", Outcome::Refuted(Failed::Holds)),
    ] {
        let (o, n) = indices(&i, subject, "bounded", subject);
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let normal = object_law_transport(
            Arc::clone(&i),
            &d,
            o,
            n,
            &mut Control::new(Limits::default(), move |p| {
                if p == Checkpoint::ObjectLawTransport {
                    seen.set(seen.get() + 1);
                }
                Usage::default()
            }),
        )
        .unwrap();
        let total = count.get();
        assert!(total >= 6);
        for at in [total - 2, total - 1, total] {
            for mode in 0..4 {
                let count = Rc::new(Cell::new(0));
                let seen = count.clone();
                let mut c = Control::new(
                    Limits {
                        time_ms: Some(1),
                        memory_mib: Some(1),
                    },
                    move |p| {
                        if p == Checkpoint::ObjectLawTransport {
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
                let Error::Stopped {
                    reason,
                    operation,
                    partial: Some(p),
                    evaluation,
                } = object_law_transport(Arc::clone(&i), &d, o, n, &mut c).unwrap_err()
                else {
                    panic!()
                };
                assert_eq!(reason, c.stop_reason().unwrap());
                assert!(evaluation.is_none());
                operation.recheck(&i, &mut quiet()).unwrap();
                let ObjectEvaluationOutcome::Evaluated(e) = p.source().unwrap().outcome() else {
                    panic!()
                };
                let ObjectEvaluationOutcome::Evaluated(original) =
                    normal.source().unwrap().outcome()
                else {
                    panic!()
                };
                assert_eq!(e.wire(), original.wire());
                assert_eq!(p.source_reading(), normal.source_reading());
                if at == total - 2 {
                    assert!(p.target().is_none());
                    assert!(p.target_reading().is_none());
                } else {
                    let ObjectEvaluationOutcome::Evaluated(e) = p.target().unwrap().outcome()
                    else {
                        panic!()
                    };
                    let ObjectEvaluationOutcome::Evaluated(original) =
                        normal.target().unwrap().outcome()
                    else {
                        panic!()
                    };
                    assert_eq!(e.wire(), original.wire());
                    assert_eq!(p.target_reading(), normal.target_reading());
                }
                assert_eq!(
                    p.outcome(),
                    if at == total { Some(&expected) } else { None }
                );
                assert_eq!(count.get(), at);
                assert!(matches!(
                    object_law_transport(Arc::clone(&i), &d, o, n, &mut c),
                    Err(Error::Construction(ConstructionFailure::Stopped(_)))
                ));
                assert_eq!(count.get(), at);
            }
        }
    }
}

#[test]
fn target_object_and_instance_failures_keep_the_base_configuration_operation() {
    let d = include_bytes!("fixtures/cross-kind-transport.atoms.json");
    let defs = archsig::definition::check_definitions(&[("definition0", d)]).unwrap();
    let digest = &defs.vocabularies["V"].digest;
    let law = "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Read { use vocabulary V version \"1\" digest \"@DIGEST@\"; law required probe(s: V.S): false; }";
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
    let r = object_law_transport(Arc::clone(&i), &ds, o, n, &mut quiet()).unwrap();
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
    let r = object_law_transport(Arc::clone(&i), &declarations(&i), o, n, &mut quiet()).unwrap();
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
