fn dependent_private_fixture(body: &str, flags: [Option<bool>; 2], unknown: bool) -> InputSources {
    let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Dep","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Dep.Root","meaning":"根。","parameters":[],"fields":[],"alignments":[]},{"kind":"entity","name":"Dep.Child","meaning":"根に属する対象。","parameters":[{"name":"owner","type":["Ref","Dep.Root"],"meaning":"所属。"}],"fields":[],"alignments":[]},{"kind":"entity","name":"Dep.Leaf","meaning":"同じ根に属する別の対象。","parameters":[{"name":"owner","type":["Ref","Dep.Root"],"meaning":"所属。"}],"fields":[{"name":"ok","type":"Bool","meaning":"観測条件。"}],"alignments":[]}]}]}"#;
    let checked =
        crate::definition::check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Dep"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Inspect {{ use vocabulary Dep version \"1\" digest \"{digest}\"; {body} }}"
    );
    let subjects = [
        ("A", "Root"),
        ("B", "Root"),
        ("Z", "Root"),
        ("p", "Child"),
        ("q", "Child"),
        ("l", "Leaf"),
        ("m", "Leaf"),
    ]
    .map(|(id, ty)| format!(r#"{{"id":"{id}","type":"Dep.{ty}","origin":"scan"}}"#))
    .join(",");
    let mut atoms = Vec::new();
    for (id, ty, owner) in [
        ("p", "Child", "A"),
        ("q", "Child", "B"),
        ("l", "Leaf", "A"),
        ("m", "Leaf", "B"),
    ] {
        if unknown && id == "p" {
            continue;
        }
        atoms.push(format!(r#"{{"id":"{id}-owner","subject":"{id}","field":"Dep.{ty}.owner","value":["v","{owner}"],"origin":"scan"}}"#));
    }
    for (id, flag) in ["l", "m"].into_iter().zip(flags) {
        if let Some(flag) = flag {
            atoms.push(format!(r#"{{"id":"{id}-ok","subject":"{id}","field":"Dep.Leaf.ok","value":{flag},"origin":"scan"}}"#));
        }
    }
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Dep","version":"1","digest":"{digest}"}}],"sources":[{{"id":"source","uri":"urn:fixture:dependent-extra","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],"origins":[{{"id":"scan","mode":"observed","method":"有限な対象と所属の観測。","locations":[{{"source":"source","path":"dependent.model","span":[0,1]}}]}}],"snapshots":[{{"id":"v","origin":"scan","subjects":[{subjects}],"atoms":[{}]}}]}}"#,
        atoms.join(",")
    );
    InputSources::from_bytes(
        vec![definitions.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
const DEPENDENT_BODY: &str = "law required chain(a:Root,b:Child[a],c:Leaf[a]) when true:c.ok;";
fn dependent_private_example(
    body: &str,
    asks: &[&str],
    flags: [Option<bool>; 2],
) -> ObservedEvaluation {
    let result = evaluate_observed_bytes(
        dependent_private_fixture(body, flags, false),
        asks,
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_ne!(result.status(), "error", "{:?}", result.issues);
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    result
}

#[test]
fn dependent_family_missing_body_and_counterexample_remain_distinct_and_rechecked() {
    let result = dependent_private_example(
        DEPENDENT_BODY,
        &["all=check(Inspect.chain)"],
        [None, Some(false)],
    );
    assert_eq!(result.answers[0].status, Decision::Refuted);
    assert!(
        result.answers[0]
            .reasons
            .iter()
            .flat_map(|r| &r.missing)
            .any(|f| f.subject == "l" && f.field.as_deref() == Some("Dep.Leaf.ok"))
    );
    let counter = result
        .nodes
        .iter()
        .enumerate()
        .find_map(|(index, node)| {
            (result.contexts[index].request == 0
                && result.contexts[index].case.is_none()
                && matches!(node.payload, Some(Payload::Counterexample { .. })))
            .then_some(index)
        })
        .unwrap();
    assert!(result.contexts[counter].instance.is_some());
    completion_mutation(&result, counter, |nodes| {
        let Some(Payload::Counterexample { facts, .. }) = &mut nodes[counter].payload else {
            unreachable!()
        };
        facts.pop();
    });
    let missing = result
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (!n.reasons.is_empty()
                && matches!(n.payload, Some(Payload::Evaluation { .. }))
                && n.reasons.iter().any(|r| !r.missing.is_empty()))
            .then_some(i)
        })
        .unwrap();
    completion_mutation(&result, missing, |nodes| {
        nodes[missing].reasons[0].missing[0].subject = "m".into();
    });
}

fn dependent_private_body_phase_stop(declaration: &str, phase: &'static str, at: usize) {
    use std::{cell::Cell, rc::Rc};
    let body = format!(
        "view seed():Unit=unit; law required prior():false; view hole(c:Leaf):Bool=c.ok; {declaration}"
    );
    let asks = [
        "seed=evaluate(Inspect.seed)",
        "prior=check(Inspect.prior)",
        "hole=evaluate(Inspect.hole,c=@v/l)",
        "current=check(Inspect.chain)",
        "later=evaluate(Inspect.seed)",
    ];
    let inputs = dependent_private_fixture(&body, [None, Some(false)], false);
    let mut quiet = named_call_quiet();
    let prepared = prepare_observed(inputs.clone(), &asks, &mut quiet).unwrap();
    let target = prepared.inputs().law().declarations["Inspect.chain"].span;
    let normal = evaluate_observed(prepared, &mut quiet).unwrap();
    assert_eq!(normal.status(), "partial", "{:?}", normal.issues);
    assert_eq!(normal.answers[1].status, Decision::Refuted);
    assert_eq!(normal.answers[2].status, Decision::Undetermined);
    assert_eq!(normal.answers[3].status, Decision::Refuted);
    assert!(
        normal.answers[2]
            .reasons
            .iter()
            .flat_map(|r| &r.missing)
            .any(|f| f.subject == "l" && f.field.as_deref() == Some("Dep.Leaf.ok"))
    );
    let expected = crate::result::Signal::Term;
    let armed = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let seen = Rc::new(Cell::new(false));
    let (arm, count, freeze) = (armed.clone(), probes.clone(), frozen.clone());
    let mut control = Control::new(move |checkpoint| {
        count.set(count.get() + 1);
        if arm.replace(false) {
            assert_eq!(checkpoint, Checkpoint::FiniteIteration);
            assert!(freeze.replace(Some(count.get())).is_none());
            Some(crate::result::Signal::Term)
        } else {
            None
        }
    });
    let prepared = prepare_observed(inputs, &asks, &mut control).unwrap();
    let stopped = evaluate_observed_with_validator(
        prepared,
        &mut control,
        |environment, graph, request, answer| {
            environment.validate_answer(graph, request, answer)?;
            if request.id == "hole" && phase != "answer" {
                let (arm, observed) = (armed.clone(), seen.clone());
                data::observe_iterations(move |span, context, operation, index| {
                    if span == target
                        && context.request == 3
                        && context.case.is_none()
                        && operation == phase
                        && index == at
                    {
                        assert!(!observed.replace(true));
                        arm.set(true);
                    }
                });
            }
            if request.id == "current" && phase == "answer" {
                assert!(!seen.replace(true));
                armed.set(true);
            }
            Ok(())
        },
    );
    data::clear_iteration_observer();
    let stopped = stopped.unwrap();
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted", "{:?}", stopped.issues);
    assert_eq!(control.stop_reason(), Some(expected));
    let retained = if phase == "answer" { 4 } else { 3 };
    assert_eq!(&stopped.answers[..retained], &normal.answers[..retained]);
    for answer in &stopped.answers[retained..] {
        assert_eq!(answer.status, Decision::Undetermined);
        assert!(answer.outputs.is_empty() && answer.claim.is_none() && answer.evidence.is_empty());
        let reason = answer
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(actual) if actual==&expected))
            .unwrap();
        let Json::Obj(ref reason_wire) = reason.wire() else {
            unreachable!()
        };
        let Json::Obj(ref expected_wire) = expected.issue() else {
            unreachable!()
        };
        assert_eq!(reason_wire["details"], expected_wire["details"]);
    }
    if phase != "answer" {
        assert!(
            !stopped
                .nodes
                .iter()
                .enumerate()
                .any(|(i, n)| stopped.contexts[i].request == 3
                    && stopped.contexts[i].instance.is_none()
                    && matches!(n.payload, Some(Payload::FiniteExhaustion { .. })))
        );
        if phase == "dependent_aggregate" {
            assert!(
                stopped
                    .nodes
                    .iter()
                    .enumerate()
                    .any(|(i, n)| stopped.contexts[i].request == 3
                        && stopped.contexts[i].instance.is_some()
                        && matches!(n.payload, Some(Payload::Counterexample { .. })))
            );
        }
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}

const DEPENDENT_NUMERIC_BODY: &str = "law required chain(z:Z,a:Root,b:Child[a],q:Q,c:Leaf[a]):if c.ok then z+1=z+1 and q+1=q+1 else z+1=z+2;";
#[test]
fn dependent_numeric_family_domain_cancel_keeps_strict_prefix_and_prior_answers() {
    dependent_private_body_phase_stop(DEPENDENT_NUMERIC_BODY, "dependent_domain_done", 1);
}
