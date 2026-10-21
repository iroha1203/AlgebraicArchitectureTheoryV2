use archsig::{
    canonical::Json,
    construction::{
        ConstructionFailure, construct,
        readings::{
            ObjectEvaluation, ObjectEvaluationFailure, ObjectEvaluationOutcome,
            ObjectReadingInstances, evaluate_object_instance, object_reading_instances,
        },
    },
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed,
        input::{CheckedInputs, InputSources, check_inputs},
        prepare_shared_observed,
    },
};
use std::sync::Arc;
const D: &[u8] = include_bytes!("fixtures/object-instances.atoms.json");
const A: &str = include_str!("fixtures/object-instances.archmap.json");
const L: &str = include_str!("fixtures/object-evaluation.law");
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn inputs(law: &str, map: &str) -> Arc<CheckedInputs> {
    let d = archsig::definition::check_definitions(&[("definition0", D)]).unwrap();
    let digest = &d.vocabularies["Instances"].digest;
    Arc::new(
        check_inputs(
            InputSources::from_bytes(
                vec![D.to_vec()],
                law.replace("@INSTANCES_DIGEST@", digest).into_bytes(),
                map.replace("@INSTANCES_DIGEST@", digest).into_bytes(),
            ),
            &mut quiet(),
        )
        .unwrap(),
    )
}
fn plan(i: &CheckedInputs) -> ObjectReadingInstances {
    let c = construct(i, "Selected", "v", "A", &mut quiet()).unwrap();
    object_reading_instances(i, &c, &mut quiet()).unwrap()
}
fn indices(p: &ObjectReadingInstances, object: &str, name: &str, subject: &str) -> (usize, usize) {
    let o = p
        .objects()
        .iter()
        .position(|o| o.identity().subject().subject == object)
        .unwrap();
    let r = p
        .instances()
        .iter()
        .position(|r| {
            r.declaration().name == format!("Selected.{name}")
                && r.bindings().iter().any(|b| b.subject().subject == subject)
        })
        .unwrap();
    (o, r)
}
fn run(i: Arc<CheckedInputs>, object: &str, name: &str, subject: &str) -> ObjectEvaluation {
    let p = plan(&i);
    let (o, r) = indices(&p, object, name, subject);
    evaluate_object_instance(i, &p, o, r, &mut quiet()).unwrap()
}
fn f<'a>(j: &'a Json, key: &str) -> &'a Json {
    let Json::Obj(m) = j else { panic!("{j:?}") };
    &m[key]
}
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(a) = j else { panic!("{j:?}") };
    a
}
fn wire(r: &ObjectEvaluation) -> Json {
    let ObjectEvaluationOutcome::Evaluated(e) = r.outcome() else {
        panic!("{:?}", r.outcome())
    };
    assert_ne!(e.status(), "error", "{:?}", f(&e.wire(), "issues"));
    assert_eq!(e.prepared().object_identity(), Some(r.object()));
    assert_eq!(e.prepared().object_instance(), Some(r.instance()));
    e.wire()
}
fn scalar(w: &Json) -> &Json {
    let a = &arr(f(w, "answers"))[0];
    assert_eq!(f(a, "status"), &Json::str("established"), "{w:?}");
    let id = f(f(f(a, "outputs"), "value"), "node");
    let n = arr(f(w, "nodes"))
        .iter()
        .find(|n| f(n, "id") == id)
        .unwrap();
    f(n, "value")
}
fn remove(map: &str, id: &str) -> String {
    let marker = format!("\"id\":\"{id}\"");
    assert_eq!(map.lines().filter(|l| l.contains(&marker)).count(), 1);
    map.lines()
        .filter(|l| !l.contains(&marker))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]")
}

#[test]
fn base_and_parts_quantify_different_subject_domains_in_the_same_evaluator() {
    let i = inputs(L, A);
    for (object, expected) in [("A", false), ("p", true), ("r", true)] {
        let r = run(
            Arc::clone(&i),
            object,
            "same",
            if object == "r" { "r" } else { "p" },
        );
        assert_eq!(scalar(&wire(&r)), &Json::Bool(expected));
    }
    for (object, expected) in [("A", false), ("p", true)] {
        assert_eq!(
            scalar(&wire(&run(Arc::clone(&i), object, "viaHelper", "p"))),
            &Json::Bool(expected)
        );
    }
    let selected = plan(&i);
    let (o, r) = indices(&selected, "p", "amount", "p");
    let read = evaluate_object_instance(Arc::clone(&i), &selected, o, r, &mut quiet()).unwrap();
    let ObjectEvaluationOutcome::Evaluated(e) = read.outcome() else {
        panic!("評価対象")
    };
    assert!(Arc::ptr_eq(&i, &e.prepared().shared_inputs()));
    let r = run(Arc::clone(&i), "A", "root", "A");
    assert_eq!(scalar(&wire(&r)), &Json::Bool(true));
    // 同じ宣言でも通常の観測環境はB/qを含む全snapshotの登録族。
    let p = prepare_shared_observed(
        Arc::clone(&i),
        &["plain=evaluate(Selected.root,a=@v/A)"],
        &mut quiet(),
    )
    .unwrap();
    assert!(p.object_identity().is_none());
    let r = evaluate_observed(p, &mut quiet()).unwrap();
    assert_eq!(scalar(&r.wire()), &Json::Bool(false));
}
#[test]
fn external_helpers_and_composite_scalar_reference_leaves_keep_their_full_domains() {
    let i = inputs(L, A);
    for name in ["allExternal", "composite"] {
        assert_eq!(
            scalar(&wire(&run(Arc::clone(&i), "p", name, "p"))),
            &Json::Bool(false)
        );
    }
    let r = run(Arc::clone(&i), "p", "external", "p");
    assert_eq!(scalar(&wire(&r)), &Json::str("11"));
    let r = run(i, "A", "owned", "A");
    assert_eq!(scalar(&wire(&r)), &Json::Bool(true));
}
#[test]
fn non_application_empty_local_quantification_and_missing_values_stay_distinct() {
    let i = inputs(L, A);
    assert!(matches!(
        run(Arc::clone(&i), "r", "amount", "p").outcome(),
        ObjectEvaluationOutcome::NotApplicable
    ));
    assert_eq!(
        scalar(&wire(&run(Arc::clone(&i), "p", "empty", "p"))),
        &Json::Bool(true)
    );
    let missing = inputs(L, &remove(A, "p-quantity"));
    let r = run(missing, "p", "amount", "p");
    let w = wire(&r);
    assert_eq!(
        f(&arr(f(&w, "answers"))[0], "status"),
        &Json::str("undetermined")
    );
    assert!(
        arr(f(&w, "issues"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("missing_observation"))
    );
}
#[test]
fn conditional_membership_is_retained_without_running_an_unestablished_instance() {
    let i = inputs(L, &remove(&remove(A, "e-to"), "r-owner"));
    let r = run(Arc::clone(&i), "A", "amount", "r");
    let ObjectEvaluationOutcome::Conditional(c) = r.outcome() else {
        panic!("{:?}", r.outcome())
    };
    assert_eq!(c.len(), 1);
    assert_eq!(c[0].slot().subject, "r");
    assert_eq!(c[0].owner().subject, "A");
    let r = run(Arc::clone(&i), "A", "same", "p");
    let w = wire(&r);
    assert_eq!(
        f(&arr(f(&w, "answers"))[0], "status"),
        &Json::str("undetermined")
    );
    assert_eq!(
        scalar(&wire(&run(i, "A", "tautology", "p"))),
        &Json::Bool(true)
    );
}
#[test]
fn finite_and_affine_remaining_parameters_use_the_existing_whole_family() {
    let i = inputs(L, A);
    let r = run(Arc::clone(&i), "p", "bounded", "p");
    let w = wire(&r);
    assert_eq!(
        f(&arr(f(&w, "answers"))[0], "status"),
        &Json::str("established"),
        "{:?}",
        f(&w, "issues")
    );
    let r = run(i, "p", "guarded", "p");
    let w = wire(&r);
    assert_eq!(
        f(&arr(f(&w, "answers"))[0], "status"),
        &Json::str("refuted")
    );
    assert!(
        arr(f(&w, "nodes"))
            .iter()
            .any(|n| f(n, "type") == &Json::str("Domain")
                && arr(f(f(n, "value"), "elements")).len() == 2)
    );
}

#[test]
fn unbound_view_family_is_an_explicit_implementation_failure_with_its_full_parameters() {
    let i = inputs(L, A);
    let p = plan(&i);
    let (o, r) = indices(&p, "p", "flag", "p");
    let Err(ObjectEvaluationFailure::NotImplemented { object, instance }) =
        evaluate_object_instance(i, &p, o, r, &mut quiet())
    else {
        panic!("未実装のview族を入力不正・成立・数学的未決にしない")
    };
    assert_eq!(object.subject().subject, "p");
    assert_eq!(instance.parameters().len(), 1);
    assert_eq!(instance.parameters()[0].name, "b");
    assert_eq!(instance.parameters()[0].ty, archsig::types::Type::Bool);
}
#[test]
fn stale_inputs_and_invalid_indices_are_rejected_before_any_evaluation() {
    let i = inputs(L, A);
    let p = plan(&i);
    for (o, r) in [(usize::MAX, 0), (0, usize::MAX)] {
        assert!(matches!(
            evaluate_object_instance(Arc::clone(&i), &p, o, r, &mut quiet()),
            Err(ObjectEvaluationFailure::Construction(
                ConstructionFailure::InvalidSelection(_)
            ))
        ));
    }
    let changed = inputs(&L.replace("= c.quantity;", "= c.quantity + 1;"), A);
    assert!(matches!(
        evaluate_object_instance(changed, &p, 0, 0, &mut quiet()),
        Err(ObjectEvaluationFailure::Construction(
            ConstructionFailure::Inconsistent(_)
        ))
    ));
}

#[test]
fn current_quantities_optional_law_counterexamples_and_external_binding_identity_are_evaluated() {
    let changed = A.replace(
        "\"subject\":\"p\",\"field\":\"Instances.Part.quantity\",\"value\":\"2\"",
        "\"subject\":\"p\",\"field\":\"Instances.Part.quantity\",\"value\":\"3\"",
    );
    assert_ne!(changed, A);
    let i = inputs(L, &changed);
    let r = run(Arc::clone(&i), "p", "amount", "p");
    assert_eq!(scalar(&wire(&r)), &Json::str("3"));
    let r = run(Arc::clone(&i), "p", "exact", "p");
    let w = wire(&r);
    let answer = &arr(f(&w, "answers"))[0];
    assert_eq!(f(answer, "status"), &Json::str("refuted"));
    assert!(!arr(f(answer, "evidence")).is_empty());
    let p = plan(&i);
    let o = p
        .objects()
        .iter()
        .position(|o| o.identity().subject().subject == "p")
        .unwrap();
    let r = p
        .instances()
        .iter()
        .position(|r| {
            r.declaration().name == "Selected.external"
                && r.bindings().iter().any(|b| b.subject().subject == "p")
                && r.bindings().iter().any(|b| b.subject().subject == "y")
        })
        .unwrap();
    let result = evaluate_object_instance(i, &p, o, r, &mut quiet()).unwrap();
    assert_eq!(scalar(&wire(&result)), &Json::str("13"));
}

#[test]
fn fixed_object_and_expression_stops_freeze_without_consuming_unfinished_evaluations() {
    use archsig::{observed::control::Checkpoint, result::Signal};
    use std::{cell::Cell, rc::Rc};
    let i = inputs(L, A);
    let p = plan(&i);
    let (o, r) = indices(&p, "p", "same", "p");
    for point in [Checkpoint::ObjectEvaluation, Checkpoint::Expression] {
        let count = Rc::new(Cell::new(0));
        let c = Rc::clone(&count);
        let mut normal = Control::new(Limits::default(), move |at| {
            if at == point {
                c.set(c.get() + 1)
            }
            Usage::default()
        });
        evaluate_object_instance(Arc::clone(&i), &p, o, r, &mut normal).unwrap();
        let total = count.get();
        assert!(total >= 3);
        for target in [1, total / 2, total] {
            for mode in 0..4 {
                let count = Rc::new(Cell::new(0));
                let c = Rc::clone(&count);
                let mut control = Control::new(
                    Limits {
                        time_ms: (mode == 0).then_some(1),
                        memory_mib: (mode == 1).then_some(1),
                    },
                    move |at| {
                        if at == point {
                            c.set(c.get() + 1)
                        }
                        if c.get() >= target {
                            match mode {
                                0 => Usage {
                                    elapsed_ms: 2,
                                    ..Usage::default()
                                },
                                1 => Usage {
                                    memory_mib: 2,
                                    ..Usage::default()
                                },
                                2 => Usage {
                                    signal: Some(Signal::Int),
                                    ..Usage::default()
                                },
                                _ => Usage {
                                    signal: Some(Signal::Term),
                                    ..Usage::default()
                                },
                            }
                        } else {
                            Usage::default()
                        }
                    },
                );
                let result = evaluate_object_instance(Arc::clone(&i), &p, o, r, &mut control);
                assert!(control.stop_reason().is_some());
                assert_eq!(count.get(), target);
                if let Ok(result) = result {
                    let ObjectEvaluationOutcome::Evaluated(e) = result.outcome() else {
                        panic!("停止を適用外へ変えない")
                    };
                    assert_eq!(e.status(), "interrupted");
                }
                let before = count.get();
                assert!(evaluate_object_instance(Arc::clone(&i), &p, o, r, &mut control).is_err());
                assert_eq!(count.get(), before);
            }
        }
    }
}
