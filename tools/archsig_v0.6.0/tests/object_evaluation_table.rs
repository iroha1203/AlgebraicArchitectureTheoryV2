use archsig::{
    canonical::Json,
    construction::{
        ConstructionFailure, construct,
        readings::{
            ObjectEvaluation, ObjectEvaluationFailure, ObjectEvaluationOutcome,
            ObjectEvaluationPosition, ObjectEvaluationTable, ObjectReadingInstances,
            evaluate_object_instance, evaluate_object_table, object_reading_instances,
        },
    },
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        input::{CheckedInputs, InputSources, check_inputs},
    },
    result::Signal,
};
use std::{cell::Cell, rc::Rc, sync::Arc};
const D: &[u8] = include_bytes!("fixtures/object-instances.atoms.json");
const L: &str = include_str!("fixtures/object-evaluation-table.law");
const A: &str = include_str!("fixtures/object-instances.archmap.json");
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
fn field<'a>(j: &'a Json, key: &str) -> &'a Json {
    let Json::Obj(o) = j else {
        panic!("object expected")
    };
    &o[key]
}
fn array(j: &Json) -> &[Json] {
    let Json::Arr(a) = j else {
        panic!("array expected")
    };
    a
}
fn wire(e: &ObjectEvaluation) -> Json {
    let ObjectEvaluationOutcome::Evaluated(e) = e.outcome() else {
        panic!("evaluation expected")
    };
    e.wire()
}
fn status(e: &ObjectEvaluation) -> String {
    let w = wire(e);
    let Json::Str(s) = field(&array(field(&w, "answers"))[0], "status") else {
        panic!()
    };
    s.clone()
}
fn value(e: &ObjectEvaluation) -> Json {
    let w = wire(e);
    let id = field(
        field(field(&array(field(&w, "answers"))[0], "outputs"), "value"),
        "node",
    );
    let node = array(field(&w, "nodes"))
        .iter()
        .find(|n| field(n, "id") == id)
        .unwrap();
    field(node, "value").clone()
}
fn row<'a>(
    t: &'a ObjectEvaluationTable,
    object: &str,
    declaration: &str,
    subject: &str,
) -> &'a ObjectEvaluation {
    t.rows()
        .iter()
        .map(|r| r.evaluation())
        .find(|e| {
            e.object().subject().subject == object
                && e.instance().declaration().name == format!("Selected.{declaration}")
                && e.instance()
                    .bindings()
                    .iter()
                    .any(|b| b.subject().subject == subject)
        })
        .unwrap()
}
fn remove(map: &str, id: &str) -> String {
    let needle = format!("\"id\":\"{id}\"");
    assert_eq!(map.lines().filter(|l| l.contains(&needle)).count(), 1);
    map.lines()
        .filter(|l| !l.contains(&needle))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]")
}
fn stop_at(point: Checkpoint, at: usize, mode: usize) -> (Control, Rc<Cell<usize>>) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    (
        Control::new(
            Limits {
                time_ms: Some(1),
                memory_mib: Some(1),
            },
            move |p| {
                if p == point {
                    seen.set(seen.get() + 1)
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
        ),
        count,
    )
}
#[test]
fn every_object_instance_row_retains_values_refutations_and_application() {
    let a=A.replace("\"id\":\"r-quantity\",\"subject\":\"r\",\"field\":\"Instances.Part.quantity\",\"value\":\"2\"", "\"id\":\"r-quantity\",\"subject\":\"r\",\"field\":\"Instances.Part.quantity\",\"value\":\"7\"");
    assert_ne!(a, A);
    let i = inputs(L, &a);
    let p = plan(&i);
    let t = evaluate_object_table(Arc::clone(&i), &p, &mut quiet()).unwrap();
    assert!(t.is_complete());
    assert_eq!(t.pending(), None);
    assert_eq!(p.objects().len(), 3);
    assert_eq!(p.instances().len(), 12);
    assert_eq!(t.rows().len(), 36);
    for (index, r) in t.rows().iter().enumerate() {
        let pos = ObjectEvaluationPosition {
            object: index / 12,
            instance: index % 12,
        };
        assert_eq!(r.position(), pos);
        let one =
            evaluate_object_instance(Arc::clone(&i), &p, pos.object, pos.instance, &mut quiet())
                .unwrap();
        match (r.evaluation().outcome(), one.outcome()) {
            (ObjectEvaluationOutcome::NotApplicable, ObjectEvaluationOutcome::NotApplicable) => {}
            (ObjectEvaluationOutcome::Evaluated(a), ObjectEvaluationOutcome::Evaluated(b)) => {
                assert_eq!(a.wire(), b.wire())
            }
            _ => panic!("all rows must keep the single evaluator result"),
        }
    }
    for object in ["A", "p"] {
        assert_eq!(value(row(&t, object, "amount", "p")), Json::str("2"));
        assert_eq!(value(row(&t, object, "flag", "p")), Json::Bool(false));
        assert_eq!(status(row(&t, object, "exact", "p")), "established");
    }
    for name in ["exact", "affine", "finite"] {
        assert_eq!(status(row(&t, "r", name, "r")), "refuted");
    }
    assert_eq!(value(row(&t, "r", "amount", "r")), Json::str("7"));
    assert_eq!(status(row(&t, "r", "guarded", "r")), "established");
    assert!(matches!(
        row(&t, "p", "amount", "r").outcome(),
        ObjectEvaluationOutcome::NotApplicable
    ));
    t.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn missing_values_and_conditional_membership_are_kept_as_distinct_rows() {
    for (map, conditional) in [
        (remove(A, "p-quantity"), false),
        (remove(&remove(A, "e-to"), "r-owner"), true),
    ] {
        let i = inputs(L, &map);
        let p = plan(&i);
        let t = evaluate_object_table(i, &p, &mut quiet()).unwrap();
        assert!(t.is_complete());
        assert_eq!(t.rows().len(), p.objects().len() * p.instances().len());
        if conditional {
            assert!(
                matches!(row(&t,"A","amount","r").outcome(),ObjectEvaluationOutcome::Conditional(c) if c.len()==1)
            );
        } else {
            let e = row(&t, "p", "amount", "p");
            assert_eq!(status(e), "undetermined");
            assert!(
                array(field(&wire(e), "issues"))
                    .iter()
                    .any(|r| field(r, "code") == &Json::str("missing_observation"))
            );
        }
    }
}
#[test]
fn empty_instance_family_is_a_complete_empty_evaluation_table() {
    let l = L
        .lines()
        .filter(|l| {
            !l.contains("view ") && !l.contains("law required") && !l.contains("law optional")
        })
        .collect::<Vec<_>>()
        .join("\n");
    let i = inputs(&l, A);
    let p = plan(&i);
    assert!(p.instances().is_empty());
    let t = evaluate_object_table(i, &p, &mut quiet()).unwrap();
    assert!(t.is_complete());
    assert!(t.rows().is_empty());
    assert_eq!(t.pending(), None);
}
#[test]
fn unimplemented_view_families_keep_the_cause_position_and_completed_prefix() {
    let l = L.replace(
        "view flag(c: Part): Bool = false;",
        "view flag(c: Part, b: Bool): Bool = b;",
    );
    let i = inputs(&l, A);
    let p = plan(&i);
    let f = evaluate_object_table(i, &p, &mut quiet()).unwrap_err();
    let ObjectEvaluationFailure::NotImplemented { object, instance } = f.cause() else {
        panic!("implementation failure must stay explicit")
    };
    assert_eq!(object.subject().subject, "A");
    assert_eq!(instance.parameters()[0].name, "b");
    let pos = f.position().unwrap();
    let partial = f.partial().unwrap();
    assert_eq!(partial.pending(), Some(pos));
    assert!(!partial.is_complete());
    assert!(!partial.rows().is_empty());
    assert!(f.active().is_none());
    assert_eq!(
        p.instances()[pos.instance].declaration().name,
        "Selected.flag"
    );
}
#[test]
fn stale_law_tables_are_rejected_and_changed_values_are_recomputed() {
    let i = inputs(L, A);
    let p = plan(&i);
    let t = evaluate_object_table(Arc::clone(&i), &p, &mut quiet()).unwrap();
    let other = inputs(&L.replace("= c.quantity;", "= c.quantity + 1;"), A);
    let f = evaluate_object_table(other, &p, &mut quiet()).unwrap_err();
    assert!(f.partial().is_none());
    assert!(matches!(
        f.cause(),
        ObjectEvaluationFailure::Construction(ConstructionFailure::Inconsistent(_))
    ));
    let changed = inputs(L, &A.replace("\"value\":\"2\"", "\"value\":\"3\""));
    assert!(t.recheck(changed, &mut quiet()).is_err());
}
#[test]
fn fixed_table_stops_keep_exact_prefix_and_final_completion_without_new_probes() {
    let i = inputs(L, A);
    let p = plan(&i);
    let full = evaluate_object_table(Arc::clone(&i), &p, &mut quiet()).unwrap();
    let n = full.rows().len();
    for at in [1, 2, 3, 2 * n + 1, 2 * n + 2] {
        for mode in 0..4 {
            let (mut c, probes) = stop_at(Checkpoint::ObjectEvaluationTable, at, mode);
            let f = evaluate_object_table(Arc::clone(&i), &p, &mut c).unwrap_err();
            assert!(
                matches!(f.cause(),ObjectEvaluationFailure::Construction(ConstructionFailure::Stopped(r)) if Some(r.clone())==c.stop_reason())
            );
            if at == 1 {
                assert!(f.partial().is_none());
            } else {
                let partial = f.partial().unwrap();
                let kept = ((at - 1) / 2).min(n);
                assert_eq!(partial.rows().len(), kept);
                assert_eq!(partial.is_complete(), at == 2 * n + 2);
                assert!(f.active().is_none());
                for (a, b) in partial.rows().iter().zip(full.rows()) {
                    assert_eq!(a.position(), b.position());
                    match (a.evaluation().outcome(), b.evaluation().outcome()) {
                        (
                            ObjectEvaluationOutcome::Evaluated(a),
                            ObjectEvaluationOutcome::Evaluated(b),
                        ) => assert_eq!(a.wire(), b.wire()),
                        (
                            ObjectEvaluationOutcome::NotApplicable,
                            ObjectEvaluationOutcome::NotApplicable,
                        ) => {}
                        _ => panic!(),
                    }
                }
            }
            assert!(
                evaluate_object_table(Arc::clone(&i), &p, &mut c)
                    .unwrap_err()
                    .partial()
                    .is_none()
            );
            assert_eq!(probes.get(), at);
        }
    }
}
#[test]
fn stopping_inside_a_cell_keeps_its_partial_dag_separate_from_completed_rows() {
    let i = inputs(L, A);
    let p = plan(&i);
    for mode in 0..4 {
        let (mut c, probes) = stop_at(Checkpoint::Expression, 5, mode);
        let f = evaluate_object_table(Arc::clone(&i), &p, &mut c).unwrap_err();
        assert!(f.position().is_some());
        assert!(!f.partial().unwrap().is_complete());
        let active = f
            .active()
            .expect("the evaluator must retain its partial DAG");
        let ObjectEvaluationOutcome::Evaluated(e) = active.outcome() else {
            panic!()
        };
        assert_eq!(e.status(), "interrupted");
        assert!(!array(field(&e.wire(), "nodes")).is_empty());
        assert_eq!(f.partial().unwrap().pending(), f.position());
        assert!(evaluate_object_table(Arc::clone(&i), &p, &mut c).is_err());
        assert_eq!(probes.get(), 5);
    }
}

#[test]
fn recheck_stops_during_comparison_keep_the_recomputed_complete_table() {
    let i = inputs(L, A);
    let p = plan(&i);
    let full = evaluate_object_table(Arc::clone(&i), &p, &mut quiet()).unwrap();
    let n = full.rows().len();
    // 全行再計算の2n+2 checkpointの後、一行比較ごとと末尾に検査する。
    for at in [2 * n + 3, 3 * n + 3] {
        for mode in 0..4 {
            let (mut c, probes) = stop_at(Checkpoint::ObjectEvaluationTable, at, mode);
            let f = full.recheck(Arc::clone(&i), &mut c).unwrap_err();
            assert!(
                matches!(f.cause(), ObjectEvaluationFailure::Construction(ConstructionFailure::Stopped(r)) if Some(r.clone())==c.stop_reason())
            );
            let partial = f.partial().unwrap();
            assert!(partial.is_complete());
            assert_eq!(partial.rows().len(), n);
            assert_eq!(partial.pending(), None);
            assert!(f.active().is_none());
            assert_eq!(f.position(), None);
            assert!(
                full.recheck(Arc::clone(&i), &mut c)
                    .unwrap_err()
                    .partial()
                    .is_none()
            );
            assert_eq!(probes.get(), at);
        }
    }
}

#[test]
fn empty_and_conditional_tables_reject_changed_values_and_origins() {
    let empty = L
        .lines()
        .filter(|l| {
            !l.contains("view ") && !l.contains("law required") && !l.contains("law optional")
        })
        .collect::<Vec<_>>()
        .join("\n");
    let conditional_law = L
        .lines()
        .filter(|l| {
            !l.contains("view flag") && !l.contains("law required") && !l.contains("law optional")
        })
        .collect::<Vec<_>>()
        .join("\n");
    let conditional_map = remove(
        &remove(&remove(&remove(A, "p-owner"), "r-owner"), "e-from"),
        "e-to",
    );
    for (law, map) in [
        (empty.as_str(), A),
        (conditional_law.as_str(), conditional_map.as_str()),
    ] {
        let i = inputs(law, map);
        let p = plan(&i);
        let t = evaluate_object_table(Arc::clone(&i), &p, &mut quiet()).unwrap();
        assert!(t.is_complete());
        assert_eq!(t.inputs().sources(), i.sources());
        assert!(Arc::ptr_eq(&t.shared_inputs(), &i));
        assert!(t.rows().iter().all(|r| !matches!(
            r.evaluation().outcome(),
            ObjectEvaluationOutcome::Evaluated(_)
        )));
        for changed_map in [
            map.replace("\"value\":\"2\"", "\"value\":\"3\""),
            map.replace("参照束縛の独立fixture。", "入力の由来が異なる観測。"),
        ] {
            assert_ne!(changed_map, map);
            let changed = inputs(law, &changed_map);
            assert_ne!(i.sources(), changed.sources());
            assert!(
                t.recheck(changed, &mut quiet()).is_err(),
                "original three inputs must be checked even without evaluated rows"
            );
        }
    }
}
