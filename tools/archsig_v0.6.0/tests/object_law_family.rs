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
const D: &[u8] = include_bytes!("fixtures/object-law-family.atoms.json");
const L: &str = include_str!("fixtures/object-law-family.law");
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
fn finite_type_domains_and_every_product_row_are_preserved() {
    let i = inputs(L, A);
    for (name, count) in [
        ("boolean", 2),
        ("fp", 3),
        ("unitAxis", 1),
        ("tupleAxis", 6),
        ("optionAxis", 3),
        ("setAxis", 4),
        ("dataAxis", 3),
        ("emptyAxis", 0),
        ("product", 6),
        ("references", 3),
    ] {
        let r = run(Arc::clone(&i), "p", name, "p");
        assert_eq!(r.outcome(), &Outcome::Preserved, "{name}");
        assert!(r.source_reading().is_none());
        assert!(r.target_reading().is_none());
        let family = r.family().unwrap();
        assert_eq!(family.rows().len(), count, "{name}");
        for p in family.parameters() {
            assert!(p.bijection().is_some());
            p.recheck(&i, &mut quiet()).unwrap();
        }
        for row in family.rows() {
            assert_eq!(row.outcome(), &Outcome::Preserved);
            assert_eq!(row.source_bindings().len(), r.instance().parameters().len());
            assert_eq!(
                row.source().application(),
                &LawApplication::Guard(Some(true))
            );
            assert_eq!(
                row.target().application(),
                &LawApplication::Guard(Some(true))
            );
            assert!(!row.source_evaluations().is_empty());
            assert!(!row.target_evaluations().is_empty());
        }
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
fn equal_forall_refutations_do_not_establish_pointwise_equivalence() {
    let law = L
        .replace(
            "law required boolean(d: Right.Child, q: Bool): q;",
            "law required boolean(d: Right.Child, q: Bool): not q;",
        )
        .replace(
            "law required fp(d: Right.Child, q: Fp(3)): q = 0;",
            "law required fp(d: Right.Child, q: Fp(3)): q = 1;",
        );
    let i = inputs(&law, A);
    for (name, count, failures) in [("boolean", 2, 2), ("fp", 3, 2)] {
        let r = run(Arc::clone(&i), "p", name, "p");
        assert_eq!(r.outcome(), &Outcome::Refuted(Failed::Holds));
        assert_eq!(r.family().unwrap().rows().len(), count);
        assert_eq!(
            r.family()
                .unwrap()
                .rows()
                .iter()
                .filter(|row| row.outcome() == &Outcome::Refuted(Failed::Holds))
                .count(),
            failures
        );
        for e in [r.source().unwrap(), r.target().unwrap()] {
            let ObjectEvaluationOutcome::Evaluated(e) = e.outcome() else {
                panic!()
            };
            assert_eq!(
                f(&arr(f(&e.wire(), "answers"))[0], "status"),
                &Json::str("refuted")
            );
        }
        r.operation().recheck(&i, &mut quiet()).unwrap();
        r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
    }
}

#[test]
fn parameter_guards_and_body_values_are_checked_at_each_point() {
    let i = inputs(L, A);
    let r = run(Arc::clone(&i), "p", "guarded", "p");
    assert_eq!(r.outcome(), &Outcome::Preserved);
    let rows = r.family().unwrap().rows();
    assert_eq!(rows.len(), 2);
    assert_eq!(
        rows.iter()
            .filter(|r| r.source().application().value() == Some(false))
            .count(),
        1
    );
    assert_eq!(
        rows.iter()
            .filter(|r| r.source().application().value() == Some(true))
            .count(),
        1
    );
    let law = L.replace(
        "law required guarded(d: Right.Child, q: Bool) when q: q;",
        "law required guarded(d: Right.Child, q: Bool) when true: true;",
    );
    let i = inputs(&law, A);
    let r = run(Arc::clone(&i), "p", "guarded", "p");
    assert_eq!(r.outcome(), &Outcome::Refuted(Failed::Applicability));
    assert_eq!(
        r.family()
            .unwrap()
            .rows()
            .iter()
            .filter(|r| r.outcome() == &Outcome::Refuted(Failed::Applicability))
            .count(),
        1
    );
    let i = inputs(L, A);
    let r = run(Arc::clone(&i), "r", "field", "r");
    assert_eq!(r.outcome(), &Outcome::Refuted(Failed::Holds));
    assert!(
        r.family()
            .unwrap()
            .rows()
            .iter()
            .all(|r| r.source().body() == Some(false) && r.target().body() == Some(true))
    );
}

#[test]
fn missing_body_and_finite_completion_do_not_turn_into_truth() {
    let i = inputs(L, A);
    let r = run(Arc::clone(&i), "p", "missing", "p");
    assert_eq!(r.outcome(), &Outcome::Undetermined);
    let rows = r.family().unwrap().rows();
    assert_eq!(rows.len(), 2);
    for row in rows {
        assert_eq!(row.source().application().value(), Some(true));
        assert_eq!(row.source().body(), None);
        assert_eq!(row.source().conditional(), None);
        assert_eq!(row.target().conditional(), None);
        assert_eq!(row.source_evaluations().len(), 2);
        assert_eq!(row.target_evaluations().len(), 2);
    }
    let law = L
        .replace(
            "law required missing(c: Left.Child, b: Bool): c.flag;",
            "law required missing(c: Left.Child, b: Bool) when c.flag: true;",
        )
        .replace(
            "law required missing(d: Right.Child, q: Bool): d.flag;",
            "law required missing(d: Right.Child, q: Bool) when true: true;",
        );
    let i = inputs(&law, A);
    let r = run(Arc::clone(&i), "p", "missing", "p");
    assert_eq!(r.outcome(), &Outcome::Undetermined);
    for row in r.family().unwrap().rows() {
        assert_eq!(row.source().application().value(), None);
        assert_eq!(row.source().conditional(), Some(true));
        assert_eq!(row.target().application().value(), Some(true));
    }
    let i = inputs(L, &remove(A, "p-count"));
    let r = run(Arc::clone(&i), "p", "field", "p");
    assert_eq!(r.outcome(), &Outcome::Undetermined);
    assert!(
        r.family()
            .unwrap()
            .rows()
            .iter()
            .all(|r| r.source().body().is_none())
    );
}

#[test]
fn completion_conditionals_require_agreement_for_true_false_and_unknown_cases() {
    for (expression, value) in [
        ("c.flag or not c.flag", true),
        ("c.flag and not c.flag", false),
    ] {
        let law = L
            .replace(
                "law required missing(c: Left.Child, b: Bool): c.flag;",
                &format!("law required missing(c: Left.Child, b: Bool): {expression};"),
            )
            .replace(
                "law required missing(d: Right.Child, q: Bool): d.flag;",
                &format!("law required missing(d: Right.Child, q: Bool): {value};"),
            );
        let i = inputs(&law, A);
        let r = run(Arc::clone(&i), "p", "missing", "p");
        assert_eq!(r.outcome(), &Outcome::Preserved);
        for row in r.family().unwrap().rows() {
            assert_eq!(row.source().body(), Some(value));
            assert_eq!(row.source().conditional(), Some(value));
            assert_eq!(row.target().conditional(), Some(value));
        }
        r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
    }
    let law = L
        .replace(
            "law required missing(c: Left.Child, b: Bool): c.flag;",
            "law required missing(c: Left.Child, b: Bool): if c.flag then false else c.count = 0;",
        )
        .replace(
            "law required missing(d: Right.Child, q: Bool): d.flag;",
            "law required missing(d: Right.Child, q: Bool): true;",
        );
    let i = inputs(&law, &remove(A, "p-count"));
    let r = run(Arc::clone(&i), "p", "missing", "p");
    assert_eq!(r.outcome(), &Outcome::Undetermined);
    assert_eq!(r.family().unwrap().rows().len(), 2);
    for row in r.family().unwrap().rows() {
        assert_eq!(row.source().conditional(), None);
        assert_eq!(row.source().body(), None);
        assert_eq!(row.target().conditional(), Some(true));
        assert_eq!(row.source_evaluations().len(), 2);
    }
    r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
}

#[test]
fn outside_objects_and_conditional_membership_remain_distinct_for_every_parameter() {
    let i = inputs(L, A);
    let r = run(Arc::clone(&i), "p", "boolean", "r");
    assert_eq!(r.outcome(), &Outcome::Preserved);
    assert_eq!(r.family().unwrap().rows().len(), 2);
    for row in r.family().unwrap().rows() {
        assert_eq!(row.source().application(), &LawApplication::OutsideObject);
        assert_eq!(row.target().application(), &LawApplication::OutsideObject);
        assert!(row.source_evaluations().is_empty());
        assert!(row.target_evaluations().is_empty());
    }
    r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
    let r = run(Arc::clone(&i), "p", "conditional", "p");
    assert_eq!(r.outcome(), &Outcome::Undetermined);
    assert_eq!(r.family().unwrap().rows().len(), 2);
    for row in r.family().unwrap().rows() {
        assert!(matches!(
            row.source().application(),
            LawApplication::ConditionalMembership(_)
        ));
        assert!(matches!(
            row.target().application(),
            LawApplication::ConditionalMembership(_)
        ));
        assert_eq!(row.source().body(), None);
    }
    r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
}

#[test]
fn reference_parameter_domains_use_the_actual_permutation_and_keep_failures() {
    let map = edit(
        A,
        "m-entries",
        "[[[\"v\",\"p\"],[\"v\",\"q\"]],[[\"v\",\"r\"],[\"v\",\"s\"]]]",
        "[[[\"v\",\"p\"],[\"v\",\"s\"]],[[\"v\",\"r\"],[\"v\",\"q\"]]]",
    );
    let i = inputs(L, &map);
    let r = run(Arc::clone(&i), "p", "references", "p");
    assert_eq!(r.outcome(), &Outcome::Preserved);
    let family = r.family().unwrap();
    assert_eq!(family.rows().len(), 3);
    let wires: Vec<_> = family
        .rows()
        .iter()
        .map(|row| {
            (
                row.source_bindings()[0].1.wire().canonical(),
                row.target_bindings()[0].1.wire().canonical(),
            )
        })
        .collect();
    assert!(
        wires
            .iter()
            .any(|(a, b)| a.contains("\"p\"") && b.contains("\"s\""))
    );
    assert!(
        wires
            .iter()
            .any(|(a, b)| a.contains("\"r\"") && b.contains("\"q\""))
    );
    r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
    let collision = edit(
        A,
        "m-entries",
        "[[[\"v\",\"p\"],[\"v\",\"q\"]],[[\"v\",\"r\"],[\"v\",\"s\"]]]",
        "[[[\"v\",\"p\"],[\"v\",\"q\"]],[[\"v\",\"r\"],[\"v\",\"q\"]]]",
    );
    let i = inputs(L, &collision);
    let r = run(Arc::clone(&i), "p", "references", "p");
    assert_eq!(
        r.outcome(),
        &Outcome::Refuted(Failed::ParameterType { position: 1 })
    );
    assert!(r.family().unwrap().parameters()[0].bijection().is_none());
    assert!(!r.family().unwrap().parameters()[0].failures().is_empty());
    assert!(r.source().is_none());
    r.operation().recheck(&i, &mut quiet()).unwrap();
    r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
}

#[test]
fn current_body_guard_quantity_mapping_and_parameter_domain_are_rechecked() {
    let i = inputs(L, A);
    let r = run(Arc::clone(&i), "p", "boolean", "p");
    for law in [
        L.replace("b: Bool): b;", "b: Bool): not b;"),
        L.replace("b: Bool): b;", "b: Bool) when b: b;"),
        L.replace(
            "law required boolean(c: Left.Child, b: Bool): b;",
            "law required boolean(c: Left.Child, b: Unit): true;",
        ),
    ] {
        assert!(r.recheck(inputs(&law, A), &mut quiet()).is_err());
    }
    let r = run(Arc::clone(&i), "p", "field", "p");
    assert!(
        r.recheck(
            inputs(L, &edit(A, "p-count", "\"2\"", "\"12\"")),
            &mut quiet()
        )
        .is_err()
    );
    let r = run(Arc::clone(&i), "p", "references", "p");
    let map = edit(
        A,
        "m-entries",
        "[[[\"v\",\"p\"],[\"v\",\"q\"]],[[\"v\",\"r\"],[\"v\",\"s\"]]]",
        "[[[\"v\",\"p\"],[\"v\",\"s\"]],[[\"v\",\"r\"],[\"v\",\"q\"]]]",
    );
    assert!(r.recheck(inputs(L, &map), &mut quiet()).is_err());
}

#[test]
fn fixed_family_stops_keep_completed_evaluations_and_rows_without_a_family_decision() {
    let i = inputs(L, A);
    let d = declarations(&i);
    let (o, n) = indices(&i, "p", "product", "p");
    let hits = Rc::new(Cell::new(0));
    let seen = hits.clone();
    let whole_hits = Rc::new(Cell::new(0));
    let whole_seen = whole_hits.clone();
    let normal = object_law_transport(
        Arc::clone(&i),
        &d,
        o,
        n,
        &mut Control::new(Limits::default(), move |p| {
            if p == Checkpoint::ObjectLawFamily {
                seen.set(seen.get() + 1);
            }
            if p == Checkpoint::ObjectLawTransport {
                whole_seen.set(whole_seen.get() + 1);
            }
            Usage::default()
        }),
    )
    .unwrap();
    let count = hits.get();
    assert!(count > 10);
    assert_eq!(normal.family().unwrap().rows().len(), 6);
    for mode in 0..4 {
        for at in [1, count / 2, count - 1, count] {
            let hits = Rc::new(Cell::new(0));
            let seen = hits.clone();
            let mut c = Control::new(
                Limits {
                    time_ms: Some(1),
                    memory_mib: Some(1),
                },
                move |p| {
                    if p == Checkpoint::ObjectLawFamily {
                        seen.set(seen.get() + 1);
                    }
                    let stop = p == Checkpoint::ObjectLawFamily && seen.get() == at;
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
            assert_eq!(hits.get(), at);
            assert!(p.outcome().is_none());
            operation.recheck(&i, &mut quiet()).unwrap();
            if at == count {
                assert_eq!(p.family().unwrap().rows(), normal.family().unwrap().rows());
                for (current, original) in [
                    (p.source().unwrap(), normal.source().unwrap()),
                    (p.target().unwrap(), normal.target().unwrap()),
                ] {
                    let ObjectEvaluationOutcome::Evaluated(current) = current.outcome() else {
                        panic!()
                    };
                    let ObjectEvaluationOutcome::Evaluated(original) = original.outcome() else {
                        panic!()
                    };
                    assert_eq!(current.wire(), original.wire());
                }
            }
            let before = hits.get();
            assert!(matches!(
                object_law_transport(Arc::clone(&i), &d, o, n, &mut c),
                Err(Error::Construction(ConstructionFailure::Stopped(_)))
            ));
            assert_eq!(hits.get(), before);
        }
        let hits = Rc::new(Cell::new(0));
        let seen = hits.clone();
        let last = whole_hits.get();
        let mut c = Control::new(
            Limits {
                time_ms: Some(1),
                memory_mib: Some(1),
            },
            move |p| {
                if p == Checkpoint::ObjectLawTransport {
                    seen.set(seen.get() + 1);
                }
                let stop = p == Checkpoint::ObjectLawTransport && seen.get() == last;
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
            partial: Some(p), ..
        } = object_law_transport(Arc::clone(&i), &d, o, n, &mut c).unwrap_err()
        else {
            panic!()
        };
        assert_eq!(p.outcome(), Some(normal.outcome()));
        assert_eq!(p.family(), normal.family());
    }
}
