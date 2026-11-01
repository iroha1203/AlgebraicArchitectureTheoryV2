use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/reference_completions.rs");
}
fn env(r: &ObservedEvaluation) -> Environment<'_> {
    Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut quiet(),
    )
    .unwrap()
}
fn example(stable: bool) -> ObservedEvaluation {
    let q = if stable { "equal" } else { "compare" };
    let asks = [
        format!(
            "first={}({}.{},s=@v/item)",
            if stable { "check" } else { "evaluate" },
            "RefCalc",
            q
        ),
        format!(
            "target={}({}.{},s=@v/item)",
            if stable { "check" } else { "evaluate" },
            "RefCalc",
            q
        ),
        "later=evaluate(RefCalc.seed)".into(),
    ];
    let asks: Vec<_> = asks.iter().map(String::as_str).collect();
    let r = evaluate_observed_bytes(
        fixture::input(fixture::SCRIPT, false, false),
        &asks,
        &mut quiet(),
    )
    .unwrap();
    assert_ne!(r.status(), "error", "{:?}", r.issues);
    r
}
fn mutate() {
    let r = example(false);
    let root = r.answers[1].outputs["evaluation"].0;
    let domain = r.nodes[root].arguments[1].0;
    let Some(Payload::Domain { elements, .. }) = &r.nodes[domain].payload else {
        panic!()
    };
    assert_eq!(elements.len(), 4);
    let first = elements[0].0;
    let foreign_domain = r.nodes[r.answers[0].outputs["evaluation"].0].arguments[1];
    assert_ne!(NodeRef(domain), foreign_domain);
    let cut = r.contexts.iter().position(|c| c.request == 2).unwrap();
    let request = &r.prepared.requests().requests()[1];
    let answer = &r.answers[1];
    for nodes in [&r.nodes[..cut], r.nodes.as_slice()] {
        let mut g = rebuild_for_origin_and_support_recheck(&r, nodes).unwrap();
        let e = env(&r);
        e.validate_answer(&g, request, answer).unwrap();
        let original_nodes = g.nodes.clone();
        let original_cases = g.cases.clone();
        let original_request = g.requests[1].clone();
        for kind in [0, 1, 9] {
            match kind {
                0 => {
                    let Some(Payload::Domain { elements, .. }) = &mut g.nodes[domain].payload
                    else {
                        panic!()
                    };
                    elements.pop();
                    g.nodes[domain].arguments.pop();
                }
                1 => {
                    let Some(Payload::Domain { elements, .. }) = &mut g.nodes[domain].payload
                    else {
                        panic!()
                    };
                    elements[1] = elements[0];
                    g.nodes[domain].arguments[2] = NodeRef(first);
                }
                9 => {
                    let Some(Payload::Scalar(Scalar::Tuple(values))) = &mut g.nodes[first].payload
                    else {
                        panic!()
                    };
                    values[0] = Scalar::Subject {
                        snapshot: "v".into(),
                        subject: "ghost".into(),
                        entity: "Refs.Root".into(),
                    };
                }
                _ => panic!(),
            }
            assert!(
                g.nodes != original_nodes
                    || g.cases != original_cases
                    || g.requests[1] != original_request,
                "real mutation {kind}"
            );
            assert!(
                matches!(
                    e.validate_answer(&g, request, answer),
                    Err(ValidationFailure::Internal(_))
                ),
                "same {kind}"
            );
            assert!(
                matches!(
                    env(&r).validate_answer(&g, request, answer),
                    Err(ValidationFailure::Internal(_))
                ),
                "fresh {kind}"
            );
            g.nodes = original_nodes.clone();
            g.cases = original_cases.clone();
            g.requests[1] = original_request.clone();
            e.validate_answer(&g, request, answer).unwrap();
            env(&r).validate_answer(&g, request, answer).unwrap();
        }
    }
}
#[test]
fn reference_completion_domains_reject_missing_duplicate_and_unregistered_members() {
    mutate()
}
#[test]
fn reference_completion_input_constraints_reject_unknown_duplicate_wrong_type_and_known_slots() {
    use crate::archmap::{FieldAssignment, check_completion_with_values};
    use crate::control::CheckFailure;
    let r = example(true);
    let i = r.prepared.inputs();
    let pin = |field: &str, target: &str| FieldAssignment {
        snapshot: "v".into(),
        subject: "item".into(),
        field: field.into(),
        value: Json::Arr(vec![Json::str("v"), Json::str(target)]),
    };
    for pins in [
        vec![pin("Refs.Sample.left", "ghost")],
        vec![pin("Refs.Sample.left", "item")],
        vec![pin("Refs.Sample.owner", "A")],
        vec![pin("Refs.Sample.left", "A"), pin("Refs.Sample.left", "A")],
    ] {
        assert!(matches!(
            check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(
                &i.archmap().snapshots,
                &i.law().definitions,
                &pins,
                &mut quiet()
            ),
            Err(CheckFailure::Input(_))
        ));
    }
    for target in ["A", "B"] {
        check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(
            &i.archmap().snapshots,
            &i.law().definitions,
            &[pin("Refs.Sample.left", target)],
            &mut quiet(),
        )
        .unwrap();
    }
}
#[test]
fn reference_completion_coverage_stop_keeps_cases_without_whole_claim() {
    use crate::control::Control;
    use std::{cell::Cell, rc::Rc};
    let input = fixture::input(fixture::SCRIPT, false, false);
    let asks = [
        "seed=evaluate(RefCalc.seed)",
        "prior=check(RefCalc.prior)",
        "hole=evaluate(RefCalc.choose,s=@v/item)",
        "current=check(RefCalc.equal,s=@v/item)",
        "later=evaluate(RefCalc.seed)",
    ];
    let normal = evaluate_observed_bytes(input.clone(), &asks, &mut quiet()).unwrap();
    assert_eq!(normal.status(), "partial");
    assert_eq!(normal.answers[1].status, Decision::Refuted);
    assert_eq!(normal.answers[2].status, Decision::Undetermined);
    assert_eq!(normal.answers[3].status, Decision::Established);
    let target = normal.prepared.inputs().law().declarations["RefCalc.equal"].span;
    let expected = crate::result::Signal::Term;
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut control = Control::new(move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            Some(crate::result::Signal::Term)
        } else {
            None
        }
    });
    let prepared = prepare_observed(input, &asks, &mut control).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut control, |e, g, q, a| {
        e.validate_answer(g, q, a)?;
        if q.id == "hole" {
            let (arm, hit) = (armed.clone(), seen.clone());
            data::observe_iterations(move |span, ctx, op, index| {
                if span == target
                    && ctx.request == 3
                    && ctx.case.is_none()
                    && op == "completion_coverage"
                    && index == 0
                {
                    assert!(!hit.replace(true));
                    arm.set(true);
                }
            });
        }
        Ok(())
    });
    data::clear_iteration_observer();
    let stopped = stopped.unwrap();
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted", "{:?}", stopped.issues);
    assert_eq!(control.stop_reason(), Some(expected));
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
                .any(|r| matches!(&r.kind,ReasonKind::Stop(reason)if reason==&expected))
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
fn reference_completion_owner_expression_keeps_known_fiber_and_original_missing_proof() {
    let r = owned_private_example(
        "view field(m:Migration):Set<State> =State[m.from];",
        &["value=evaluate(Reservations.field,m=@v/m)"],
        Some("m-from"),
        false,
    );
    assert_eq!(r.status(), "complete");
    let a = &r.answers[0];
    assert_eq!(a.status, Decision::Established);
    assert!(a.scope.completions);
    let value = a.outputs["value"].0;
    let Some(Payload::Scalar(Scalar::Set { element, items })) = &r.nodes[value].payload else {
        panic!()
    };
    assert_eq!(element, &Type::Ref("Reservations.State".into()));
    assert_eq!(
        items,
        &vec![
            Scalar::Subject {
                snapshot: "v".into(),
                subject: "p".into(),
                entity: "Reservations.State".into()
            },
            Scalar::Subject {
                snapshot: "v".into(),
                subject: "q".into(),
                entity: "Reservations.State".into()
            }
        ]
    );
    assert!(
        a.reasons
            .iter()
            .flat_map(|r| &r.missing)
            .any(|f| f.snapshot == "v"
                && f.subject == "m"
                && f.field.as_deref() == Some("Reservations.Migration.from"))
    );
    let root = a.outputs["evaluation"].0;
    let domain = r.nodes[root].arguments[1].0;
    let Some(Payload::Domain { elements, .. }) = &r.nodes[domain].payload else {
        panic!()
    };
    assert_eq!(elements.len(), 1);
    assert_eq!(
        r.nodes[elements[0].0].payload,
        Some(Payload::Scalar(Scalar::Subject {
            snapshot: "v".into(),
            subject: "A".into(),
            entity: "Reservations.System".into()
        }))
    );
    completion_mutation(&r, value, |ns| {
        let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut ns[value].payload else {
            panic!()
        };
        items.pop();
    });
    completion_mutation(&r, domain, |ns| {
        ns[domain].support.clear();
    });
}
