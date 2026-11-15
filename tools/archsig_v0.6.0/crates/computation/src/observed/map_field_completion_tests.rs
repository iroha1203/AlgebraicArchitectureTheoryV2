use super::*;
#[allow(dead_code)]
mod fixture {

    include!("../../../../tests/common/map_field_completions.rs");
}
fn environment(r: &ObservedEvaluation) -> Environment<'_> {
    Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &quiet(),
    )
    .unwrap()
}
fn example(mode: usize) -> ObservedEvaluation {
    let question = match mode {
        0 | 9 => "evaluate(Inspect.read,h=@v/h)",
        1 => "evaluate(Inspect.mixed,h=@v/h)",
        2 => "evaluate(Inspect.bag,h=@v/h)",
        3 => "evaluate(Inspect.choice,h=@v/h)",
        4 => "check(Inspect.valid,h=@v/h)",
        5 => "evaluate(Inspect.independent,h=@v/h)",
        6 => "evaluate(Inspect.partial,h=@v/h)",
        7 => "evaluate(Inspect.pending,h=@v/h,a=@v/B)",
        8 => "evaluate(Inspect.plain,h=@v/h)",
        _ => panic!(),
    };
    let first = format!("first={question}");
    let target = format!("target={question}");
    let r = evaluate_observed_bytes(
        fixture::input(mode == 8 || mode == 9, false, mode == 4 || mode == 6, false),
        &[&first, &target, "later=evaluate(Inspect.seed)"],
        &quiet(),
    )
    .unwrap();
    assert_ne!(r.status(), "error", "{:?}", r.answers);
    r
}
fn map_pairs_mut(value: &mut Scalar) -> &mut Vec<(Scalar, Scalar)> {
    match value {
        Scalar::Map { pairs, .. } => pairs,
        _ => panic!("Map expected"),
    }
}
fn scalar_mut(node: &mut Node) -> &mut Scalar {
    match node.payload.as_mut().unwrap() {
        Payload::Scalar(s) => std::sync::Arc::make_mut(s),
        _ => panic!("Scalar expected"),
    }
}
#[test]
fn map_field_totality_owned_key_image_and_duplicate_rows_are_rechecked() {
    let r = example(9);
    let request = &r.prepared.requests().requests()[1];
    let answer = &r.answers[1];
    let root = answer.outputs["evaluation"].0;
    let domain = r.nodes[root].arguments[1].0;
    let Some(Payload::Domain { elements, .. }) = &r.nodes[domain].payload else {
        panic!()
    };
    let first = elements
        .iter()
        .find(|m| matches!(r.nodes[m.0].scalar_payload(), Some(Scalar::Map { pairs, .. }) if !pairs.is_empty()))
        .unwrap()
        .0;
    // 全域性の再検査の代表: 候補のMapから行を消すと核が拒否する。
    let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let pairs = map_pairs_mut(scalar_mut(&mut graph.nodes[first]));
    pairs.clear();
    let t = scalar_mut(&mut graph.nodes[first]).ty();
    graph.nodes[first].ty = NodeType::Value(t);
    assert!(matches!(
        environment(&r).validate_answer(&graph, request, answer),
        Err(ValidationFailure::Internal(_))
    ));
}
#[test]
fn map_field_coverage_stop_never_promotes_unfinished_whole() {
    use archsig_common::control::Control;
    use std::{cell::Cell, rc::Rc};
    let input = fixture::input(true, false, false, false);
    let asks = [
        "seed=evaluate(Inspect.seed)",
        "prior=check(Inspect.prior)",
        "hole=evaluate(Inspect.partial,h=@v/h)",
        "current=evaluate(Inspect.same,h=@v/h)",
        "later=evaluate(Inspect.seed)",
    ];
    let normal = evaluate_observed_bytes(input.clone(), &asks, &quiet()).unwrap();
    assert_eq!(normal.status(), "partial");
    assert_eq!(normal.answers[1].status, Decision::Refuted);
    assert_eq!(normal.answers[2].status, Decision::Undetermined);
    assert_eq!(normal.answers[3].status, Decision::Established);
    let target = normal.prepared.inputs().law().declarations()["Inspect.same"].span;
    let expected = archsig_input::result::Signal::Term;
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let c = Control::new(move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            Some(archsig_input::result::Signal::Term)
        } else {
            None
        }
    });
    let prepared = prepare_observed(input, &asks, &c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &c, |e, g, q, answer| {
        e.validate_answer(g, q, answer)?;
        if q.id == "hole" {
            let (a, s) = (armed.clone(), seen.clone());
            data::observe_iterations(move |span, ctx, operation, index| {
                if span == target
                    && ctx.request == 3
                    && ctx.case.is_none()
                    && operation == "completion_coverage"
                    && index == 0
                {
                    assert!(!s.replace(true));
                    a.set(true);
                }
            });
        }
        Ok(())
    })
    .unwrap();
    data::clear_iteration_observer();
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted", "{:?}", stopped.issues);
    assert_eq!(c.stop_reason(), Some(expected));
    assert_eq!(
        stopped.frames.as_slice(),
        &normal.frames[..stopped.frames.len()]
    );
    assert_eq!(
        stopped.iterations.as_slice(),
        &normal.iterations[..stopped.iterations.len()]
    );
    assert_eq!(
        stopped.instances.as_slice(),
        &normal.instances[..stopped.instances.len()]
    );
    assert_eq!(
        stopped.cases.as_slice(),
        &normal.cases[..stopped.cases.len()]
    );
    assert_eq!(
        stopped.universal_witnesses.as_slice(),
        &normal.universal_witnesses[..stopped.universal_witnesses.len()]
    );
    let Json::Obj(ref nw) = normal.wire() else {
        panic!()
    };
    let Json::Obj(ref sw) = stopped.wire() else {
        panic!()
    };
    let Json::Arr(na) = &nw["answers"] else {
        panic!()
    };
    let Json::Arr(sa) = &sw["answers"] else {
        panic!()
    };
    assert_eq!(&sa[..3], &na[..3]);
    for a in &stopped.answers[3..] {
        assert_eq!(a.status, Decision::Undetermined);
        assert!(a.outputs.is_empty() && a.claim.is_none() && a.evidence.is_empty());
        assert!(
            a.reasons
                .iter()
                .any(|r| matches!(&r.kind,ReasonKind::Stop(s)if s==&expected))
        );
    }
    assert!(
        !stopped
            .nodes
            .iter()
            .enumerate()
            .any(|(i, n)| stopped.contexts[i].request == 3
                && stopped.contexts[i].case.is_none()
                && matches!(n.payload, Some(Payload::FiniteExhaustion { .. })))
    );
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}

#[test]
fn map_field_internal_pins_validate_original_map_shapes_refs_totality_and_missing_identity() {
    use archsig_common::control::CheckFailure;
    use archsig_input::archmap::{FieldAssignment, check_completion_with_values};
    let pin = |field: &str, value: Json| FieldAssignment {
        snapshot: "v".into(),
        subject: "h".into(),
        field: format!("MapFields.Holder.{field}"),
        value,
    };
    let r = example(9);
    let input = r.prepared.inputs();
    let kx = fixture::table("v", "k", "x");
    let row = |key: Json, image: Json| Json::Arr(vec![key, image]);
    let malformed = [
        ("table", fixture::table("v", "ghost", "x")),
        ("table", fixture::table("v", "x", "x")),
        ("table", fixture::table("v", "k", "A")),
        (
            "table",
            Json::Arr(vec![
                row(fixture::reference("v", "k"), fixture::reference("v", "x")),
                row(fixture::reference("v", "k"), fixture::reference("v", "y")),
            ]),
        ),
        (
            "table",
            Json::Arr(vec![Json::Arr(vec![fixture::reference("v", "k")])]),
        ),
        ("table", Json::Bool(true)),
        ("owner", fixture::reference("v", "A")),
        (
            "mixed",
            Json::Arr(vec![Json::Bool(false), fixture::table("v", "k", "A")]),
        ),
        ("bag", Json::Arr(vec![fixture::table("v", "x", "x")])),
        (
            "choice",
            Json::obj([
                ("tag", Json::str("wrap")),
                ("args", Json::Arr(vec![fixture::table("v", "k", "A")])),
            ]),
        ),
    ];
    for (field, value) in malformed {
        assert!(
            matches!(
                check_completion_with_values::<CheckFailure<Box<archsig_common::issue::Issue>>>(
                    &input.archmap().snapshots(),
                    &input.law().definitions(),
                    &[pin(field, value)],
                    &quiet()
                ),
                Err(CheckFailure::Input(_))
            ),
            "malformed {field}"
        );
    }
    assert!(matches!(
        check_completion_with_values::<CheckFailure<Box<archsig_common::issue::Issue>>>(
            &input.archmap().snapshots(),
            &input.law().definitions(),
            &[pin("table", kx.clone()), pin("table", kx.clone())],
            &quiet()
        ),
        Err(CheckFailure::Input(_))
    ));
    for bad in [
        Json::Arr(vec![]),
        fixture::table("w", "k", "x"),
        Json::Arr(vec![row(
            fixture::reference("v", "k"),
            fixture::reference("w", "x"),
        )]),
        Json::Arr(vec![
            row(fixture::reference("v", "k"), fixture::reference("v", "x")),
            row(fixture::reference("w", "k"), fixture::reference("v", "y")),
        ]),
    ] {
        assert!(
            matches!(check_completion_with_values::<CheckFailure<Box<archsig_common::issue::Issue>>>(&input.archmap().snapshots(),&input.law().definitions(),&[pin("table",bad)],&quiet()),Err(CheckFailure::Input(issue)) if issue.code==archsig_common::issue::Code::InconsistentObservation)
        );
    }
    for good in [kx, fixture::table("v", "k", "y")] {
        check_completion_with_values::<CheckFailure<Box<archsig_common::issue::Issue>>>(
            &input.archmap().snapshots(),
            &input.law().definitions(),
            &[pin("table", good)],
            &quiet(),
        )
        .unwrap();
    }
    let unknown = example(4);
    let input = unknown.prepared.inputs();
    check_completion_with_values::<CheckFailure<Box<archsig_common::issue::Issue>>>(
        &input.archmap().snapshots(),
        &input.law().definitions(),
        &[pin("table", Json::Arr(vec![]))],
        &quiet(),
    )
    .unwrap();
    assert!(
        matches!(check_completion_with_values::<CheckFailure<Box<archsig_common::issue::Issue>>>(&input.archmap().snapshots(),&input.law().definitions(),&[pin("table",Json::Arr(vec![])),pin("owner",fixture::reference("v","A"))],&quiet()),Err(CheckFailure::Input(issue)) if issue.code==archsig_common::issue::Code::InconsistentObservation)
    );
}

#[test]
fn prepared_completion_keeps_pin_outcomes_bound_to_each_candidate_and_input() {
    use archsig_common::control::{CheckFailure, Checkpoint, Control, Signal};
    use archsig_common::issue::{Code, Issue};
    use archsig_input::archmap::{CompletionPreparation, FieldAssignment};
    type Checked = CheckFailure<Box<Issue>>;

    let pin = |name, value| FieldAssignment {
        snapshot: "v".into(),
        subject: "h".into(),
        field: format!("MapFields.Holder.{name}"),
        value,
    };
    let empty = || pin("table", Json::Arr(vec![]));
    let owner = |id| pin("owner", fixture::reference("v", id));
    let input = example(4);
    let other = example(9);
    let control = quiet();
    let input = input.prepared.inputs();
    let other = other.prepared.inputs();
    let prepared = CompletionPreparation::new(input, &control, Checkpoint::Completion).unwrap();
    let fixed = CompletionPreparation::new(other, &control, Checkpoint::Completion).unwrap();

    assert!(prepared.check::<Checked>(&[owner("A")], &control).is_ok());
    assert!(prepared.check::<Checked>(&[empty()], &control).is_ok());
    assert!(matches!(
        prepared.check::<Checked>(&[owner("A"), empty()], &control),
        Err(CheckFailure::Input(issue)) if issue.code == Code::InconsistentObservation
    ));
    assert!(matches!(
        fixed.check::<Checked>(&[owner("B"), empty()], &control),
        Err(CheckFailure::Input(issue)) if issue.code == Code::Reference
    ));
    use std::{cell::Cell, rc::Rc};
    let pins = [owner("B"), empty()];
    for warm in [false, true] {
        let run = |stop_at| {
            let candidate =
                CompletionPreparation::new(input, &control, Checkpoint::Completion).unwrap();
            if warm {
                candidate.check::<Checked>(&pins, &control).unwrap();
            }
            let checkpoints = Rc::new(Cell::new(0_usize));
            let observed = checkpoints.clone();
            let control = Control::new(move |_| {
                observed.set(observed.get() + 1);
                (stop_at == Some(observed.get())).then_some(Signal::Term)
            });
            let result = candidate.check::<Checked>(&pins, &control);
            candidate.check::<Checked>(&pins, &quiet()).unwrap();
            (result, checkpoints.get())
        };
        let (result, checkpoints) = run(None);
        result.unwrap();
        for at in 1..=checkpoints {
            assert!(
                matches!(run(Some(at)).0, Err(CheckFailure::Stopped(Signal::Term))),
                "warm={warm}, checkpoint={at}"
            );
        }
    }
}

#[test]
fn direct_completion_uses_the_subject_coordinate_in_both_indexes() {
    use archsig_common::{control::CheckFailure, issue::Issue, names::QualifiedName};
    use archsig_input::archmap::{
        Field, FieldAssignment, Snapshot, Subject, check_completion_with_values,
        check_valuation_with_values,
    };
    type Checked = CheckFailure<Box<Issue>>;

    let subject = |id: &str, ty: &str, fields| Subject {
        id: id.into(),
        snapshot: "v".into(),
        ty: QualifiedName::parse(format!("MapFields.{ty}")),
        origin: "v".into(),
        fields,
        pointer: "/subjects".into(),
    };
    let snapshots = [Snapshot {
        id: "container".into(),
        origin: "v".into(),
        subjects: vec![
            subject("A", "Root", vec![]),
            subject(
                "k",
                "Key",
                vec![Field {
                    name: QualifiedName::parse("MapFields.Key.owner".into()),
                    ty: Type::Ref("MapFields.Root".into()),
                    slot: Slot::Missing,
                }],
            ),
        ],
    }];
    let candidate = [FieldAssignment {
        snapshot: "v".into(),
        subject: "k".into(),
        field: "MapFields.Key.owner".into(),
        value: fixture::reference("v", "A"),
    }];
    let result = example(4);
    let definitions = result.prepared.inputs().definitions();
    check_completion_with_values::<Checked>(&snapshots, definitions, &candidate, &quiet()).unwrap();
    check_valuation_with_values::<Checked>(&snapshots, definitions, &candidate, &quiet()).unwrap();
}

#[test]
fn direct_valuation_checks_replacement_without_reading_the_original_map() {
    use archsig_common::{control::CheckFailure, issue::Issue, names::QualifiedName};
    use archsig_input::archmap::{
        Field, FieldAssignment, Snapshot, Subject, check_valuation_with_values, value::Value,
    };

    let result = example(8);
    let input = result.prepared.inputs();
    let subject = |id: &str, ty: &str, fields| Subject {
        id: id.into(),
        snapshot: "v".into(),
        ty: QualifiedName::parse(format!("MapFields.{ty}")),
        origin: "v".into(),
        fields,
        pointer: format!("/subjects/{id}"),
    };
    let reference = |id: &str| Value::Ref {
        snapshot: "v".into(),
        subject: id.into(),
    };
    let snapshots = [Snapshot {
        id: "v".into(),
        origin: "v".into(),
        subjects: vec![
            subject("k", "Key", vec![]),
            subject("i", "Image", vec![]),
            subject(
                "h",
                "Holder",
                vec![Field {
                    name: QualifiedName::parse("MapFields.Holder.plain".into()),
                    ty: Type::Map(
                        Box::new(Type::Ref("MapFields.Key".into())),
                        Box::new(Type::Ref("MapFields.Image".into())),
                    ),
                    slot: Slot::Known {
                        atom: "previous".into(),
                        origin: "v".into(),
                        pointer: "/previous/table".into(),
                        value: Value::Map(vec![(reference("unregistered"), reference("i"))]),
                    },
                }],
            ),
        ],
    }];
    let candidate = [FieldAssignment {
        snapshot: "v".into(),
        subject: "h".into(),
        field: "MapFields.Holder.plain".into(),
        value: fixture::table("v", "k", "i"),
    }];
    check_valuation_with_values::<CheckFailure<Box<Issue>>>(
        &snapshots,
        input.definitions(),
        &candidate,
        &quiet(),
    )
    .unwrap();
}
