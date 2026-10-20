use archsig::{
    canonical::Json,
    construction::{construct, readings::object_reading_instances},
    observed::{
        PrepareFailure, PreparedObserved,
        control::{Checkpoint, Control, Limits, Usage},
        evaluate_observed,
        input::{CheckedInputs, InputSources, check_inputs},
        prepare_checked_observed, prepare_observed, prepare_shared_observed,
        request::{RequestIssueCode, ResolveFailure},
        result::ObservedEvaluation,
    },
    result::Signal,
};
use std::{cell::Cell, rc::Rc, sync::Arc};
const D: &[u8] = include_bytes!("fixtures/counter.atoms.json");
const L: &[u8] = include_bytes!("fixtures/counter.law");
const A: &str = include_str!("fixtures/counter.archmap.json");
fn sources(count: &str) -> InputSources {
    InputSources::from_bytes(
        vec![D.to_vec()],
        L.to_vec(),
        A.replace("\"value\": \"2\"", &format!("\"value\": \"{count}\""))
            .into_bytes(),
    )
}
fn checked(count: &str) -> Arc<CheckedInputs> {
    Arc::new(check_inputs(sources(count), &mut Control::unlimited()).unwrap())
}
fn field<'a>(value: &'a Json, key: &str) -> &'a Json {
    let Json::Obj(fields) = value else {
        panic!("object: {value:?}")
    };
    fields
        .get(key)
        .unwrap_or_else(|| panic!("{key}: {value:?}"))
}
fn array(value: &Json) -> &[Json] {
    let Json::Arr(values) = value else {
        panic!("array: {value:?}")
    };
    values
}
fn assert_number(result: &ObservedEvaluation, expected: &str) {
    let wire = result.wire();
    let answer = &array(field(&wire, "answers"))[0];
    assert_eq!(field(answer, "status"), &Json::str("established"));
    let reference = field(field(field(answer, "outputs"), "value"), "node");
    let node = array(field(&wire, "nodes"))
        .iter()
        .find(|n| field(n, "id") == reference)
        .unwrap();
    assert_eq!(field(node, "type"), &Json::str("Z"));
    assert_eq!(field(node, "state"), &Json::str("value"));
    assert_eq!(field(node, "value"), &Json::str(expected));
}
fn prepare(shared: &Arc<CheckedInputs>, texts: &[&str]) -> PreparedObserved {
    prepare_shared_observed(Arc::clone(shared), texts, &mut Control::unlimited()).unwrap()
}
#[test]
fn preparations_and_results_share_the_original_tables_without_input_checkpoints() {
    fn send_sync<T: Send + Sync>() {}
    send_sync::<CheckedInputs>();
    send_sync::<PreparedObserved>();
    let shared = checked("2");
    let checks = Rc::new(Cell::new(0));
    let seen = Rc::clone(&checks);
    let mut control = Control::new(Limits::default(), move |point| {
        if matches!(
            point,
            Checkpoint::InputBundle
                | Checkpoint::BeforeDefinitions
                | Checkpoint::BeforeLaw
                | Checkpoint::BeforeArchMap
        ) {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    let first = prepare_shared_observed(
        Arc::clone(&shared),
        &["n=evaluate(CountCheck.amount,s=@v/s)"],
        &mut control,
    )
    .unwrap();
    let second = prepare_shared_observed(
        first.shared_inputs(),
        &["b=check(CountAudit.bounded,s=@v/s)"],
        &mut control,
    )
    .unwrap();
    assert!(std::ptr::eq(first.inputs(), shared.as_ref()));
    assert!(std::ptr::eq(second.inputs().law(), shared.law()));
    assert!(std::ptr::eq(
        first.inputs().archmap(),
        second.inputs().archmap()
    ));
    assert!(std::ptr::eq(
        first.inputs().definitions(),
        second.inputs().definitions()
    ));
    assert!(Arc::ptr_eq(&first.shared_inputs(), &second.shared_inputs()));
    let first = evaluate_observed(first, &mut control).unwrap();
    let second = evaluate_observed(second, &mut control).unwrap();
    assert_number(&first, "2");
    assert_eq!(second.status(), "complete");
    assert!(Arc::ptr_eq(
        &first.prepared().shared_inputs(),
        &second.prepared().shared_inputs()
    ));
    assert_eq!(checks.get(), 0);
}
#[test]
fn object_instances_use_the_same_bundle_for_multiple_actual_view_evaluations() {
    let d = include_bytes!("fixtures/object-instances.atoms.json");
    let definitions = archsig::definition::check_definitions(&[("definition0", d)]).unwrap();
    let digest = &definitions.vocabularies["Instances"].digest;
    let shared = Arc::new(
        check_inputs(
            InputSources::from_bytes(
                vec![d.to_vec()],
                include_str!("fixtures/object-instances.law")
                    .replace("@INSTANCES_DIGEST@", digest)
                    .into_bytes(),
                include_str!("fixtures/object-instances.archmap.json")
                    .replace("@INSTANCES_DIGEST@", digest)
                    .into_bytes(),
            ),
            &mut Control::unlimited(),
        )
        .unwrap(),
    );
    let c = construct(&shared, "Selected", "v", "A", &mut Control::unlimited()).unwrap();
    let instances = object_reading_instances(&shared, &c, &mut Control::unlimited()).unwrap();
    assert_eq!(
        instances
            .instances()
            .iter()
            .filter(|i| i.declaration().name == "Selected.amount")
            .map(|i| i.bindings()[0].subject().subject.as_str())
            .collect::<Vec<_>>(),
        ["p", "r"]
    );
    let first = prepare(&shared, &["n=evaluate(Selected.amount,c=@v/p)"]);
    let second = prepare(&shared, &["n=evaluate(Selected.amount,c=@v/r)"]);
    let first = evaluate_observed(first, &mut Control::unlimited()).unwrap();
    let second = evaluate_observed(second, &mut Control::unlimited()).unwrap();
    assert_number(&first, "2");
    assert_number(&second, "2");
    assert!(std::ptr::eq(
        first.prepared().inputs(),
        second.prepared().inputs()
    ));
    assert_eq!(
        instances.source_law(),
        first.prepared().inputs().sources().law()
    );
    for result in [&first, &second] {
        let wire = result.wire();
        let raw = result.prepared().inputs().sources().law().bytes();
        let mut occurrences = std::collections::BTreeSet::new();
        for node in array(field(&wire, "nodes")) {
            if field(node, "type") != &Json::str("Expression") {
                continue;
            }
            let Json::Obj(value) = field(node, "value") else {
                continue;
            };
            let Some(location) = value.get("location") else {
                continue;
            };
            if field(location, "input") != &Json::str("law") {
                continue;
            }
            let span = array(field(location, "span"));
            let (Json::Nat(start), Json::Nat(end)) = (&span[0], &span[1]) else {
                panic!("span")
            };
            occurrences.insert(&raw[*start as usize..*end as usize]);
        }
        assert_eq!(
            occurrences,
            std::collections::BTreeSet::from([b"c".as_slice(), b"c.quantity".as_slice()])
        );
    }
}
#[test]
fn results_keep_sources_alive_after_original_handles_are_dropped() {
    let shared = checked("2");
    let weak = Arc::downgrade(&shared);
    let first = prepare(&shared, &["n=evaluate(CountCheck.amount,s=@v/s)"]);
    let second = prepare(&shared, &["b=check(CountAudit.bounded,s=@v/s)"]);
    drop(shared);
    assert!(weak.upgrade().is_some());
    let first = evaluate_observed(first, &mut Control::unlimited()).unwrap();
    let second = evaluate_observed(second, &mut Control::unlimited()).unwrap();
    assert_number(&first, "2");
    assert_eq!(first.prepared().inputs().sources().law().bytes(), L);
    assert!(
        first
            .prepared()
            .inputs()
            .inputs()
            .iter()
            .all(|i| i.bytes_digest.is_some() && i.model_digest.is_some())
    );
    drop(first);
    assert_eq!(
        second.prepared().inputs().sources().archmap().bytes(),
        A.as_bytes()
    );
    drop(second);
    assert!(weak.upgrade().is_none());
}
#[test]
fn request_batches_do_not_share_ids_answers_or_another_input_value() {
    let shared = checked("2");
    let first = evaluate_observed(
        prepare(&shared, &["n=evaluate(CountCheck.amount,s=@v/s)"]),
        &mut Control::unlimited(),
    )
    .unwrap();
    let failure = prepare_shared_observed(
        Arc::clone(&shared),
        &["p=needed($n)"],
        &mut Control::unlimited(),
    )
    .unwrap_err();
    let PrepareFailure::Requests {
        inputs,
        failure: ResolveFailure::Invalid { issues, .. },
    } = failure
    else {
        panic!("unknown prior-batch id")
    };
    assert!(Arc::ptr_eq(&inputs, &shared));
    assert_eq!(issues[0].code, RequestIssueCode::Reference);
    let another = checked("12");
    assert!(!Arc::ptr_eq(&another, &shared));
    let second = evaluate_observed(
        prepare(&another, &["n=evaluate(CountCheck.amount,s=@v/s)"]),
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_number(&first, "2");
    assert_number(&second, "12");
    let first_wire = first.wire();
    let second_wire = second.wire();
    assert_eq!(array(field(&first_wire, "requests")).len(), 1);
    assert_eq!(array(field(&second_wire, "requests")).len(), 1);
    assert_eq!(
        field(&array(field(&first_wire, "answers"))[0], "id"),
        &Json::str("n")
    );
    assert_eq!(
        field(&array(field(&second_wire, "answers"))[0], "id"),
        &Json::str("n")
    );
}
#[test]
fn request_failures_keep_the_exact_shared_bundle_and_existing_reasons() {
    let shared = checked("2");
    let failure = prepare_shared_observed(
        Arc::clone(&shared),
        &["n=evaluate(CountCheck.amount)"],
        &mut Control::unlimited(),
    )
    .unwrap_err();
    let wire = failure.wire().unwrap();
    let PrepareFailure::Requests {
        inputs,
        failure:
            ResolveFailure::Invalid {
                issues,
                stop_reason,
                ..
            },
    } = failure
    else {
        panic!("missing binding")
    };
    assert!(Arc::ptr_eq(&inputs, &shared));
    assert!(stop_reason.is_none());
    assert_eq!(issues[0].code, RequestIssueCode::MissingBinding);
    assert_eq!(issues[0].argument, "s");
    assert!(array(field(&wire, "nodes")).is_empty());
    assert!(array(field(&wire, "answers")).is_empty());
    assert_eq!(inputs.sources().law().bytes(), L);
    let recovered = evaluate_observed(
        prepare(&inputs, &["n=evaluate(CountCheck.amount,s=@v/s)"]),
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_number(&recovered, "2");
}
#[test]
fn owned_byte_and_shared_preparation_use_the_same_existing_evaluator() {
    let asks = [
        "p=needed($c)",
        "c=check(CountCheck.nonnegative)",
        "n=evaluate(CountCheck.amount,s=@v/s)",
    ];
    let shared = checked("2");
    let borrowed = prepare(&shared, &asks);
    let owned = prepare_checked_observed(
        check_inputs(sources("2"), &mut Control::unlimited()).unwrap(),
        &asks,
        &mut Control::unlimited(),
    )
    .unwrap();
    let bytes = prepare_observed(sources("2"), &asks, &mut Control::unlimited()).unwrap();
    assert_eq!(borrowed.requests(), owned.requests());
    assert_eq!(borrowed.requests(), bytes.requests());
    assert_eq!(borrowed.requests().evaluation_order(), [1, 0, 2]);
    let borrowed = evaluate_observed(borrowed, &mut Control::unlimited()).unwrap();
    let owned = evaluate_observed(owned, &mut Control::unlimited()).unwrap();
    let bytes = evaluate_observed(bytes, &mut Control::unlimited()).unwrap();
    assert_eq!(borrowed.wire(), owned.wire());
    assert_eq!(borrowed.wire(), bytes.wire());
}
#[test]
fn sharing_does_not_reset_the_control_or_probe_again_after_a_stop() {
    let shared = checked("2");
    for mode in 0..4 {
        let prepared = prepare(&shared, &["n=evaluate(CountCheck.amount,s=@v/s)"]);
        let count = Rc::new(Cell::new(0));
        let seen = Rc::clone(&count);
        let mut control = Control::new(
            Limits {
                time_ms: (mode == 0).then_some(1),
                memory_mib: (mode == 1).then_some(1),
            },
            move |point| {
                seen.set(seen.get() + 1);
                let stop = point == Checkpoint::Resolve;
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
        let failure = prepare_shared_observed(
            Arc::clone(&shared),
            &["c=check(CountCheck.nonnegative)"],
            &mut control,
        )
        .unwrap_err();
        let PrepareFailure::Requests {
            inputs,
            failure: ResolveFailure::Interrupted { reason },
        } = failure
        else {
            panic!("stop in resolution")
        };
        assert!(Arc::ptr_eq(&inputs, &shared));
        assert_eq!(Some(reason.clone()), control.stop_reason());
        let before = count.get();
        let failure =
            prepare_shared_observed(inputs, &["c=check(CountCheck.nonnegative)"], &mut control)
                .unwrap_err();
        assert!(
            matches!(failure,PrepareFailure::Requests {failure:ResolveFailure::Interrupted {reason:r},..} if r == reason)
        );
        let result = evaluate_observed(prepared, &mut control).unwrap();
        let wire = result.wire();
        assert!(array(field(&wire, "nodes")).is_empty());
        assert_eq!(
            field(&array(field(&wire, "answers"))[0], "status"),
            &Json::str("undetermined")
        );
        assert_eq!(count.get(), before);
    }
}
