use super::*;
mod owned_map_fixture {
    use crate as archsig;
    include!("../../tests/common/owned_map_calls.rs");
}
fn map_owned_result(mode: &str, asks: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(owned_map_fixture::input(mode, "r1"), asks, &mut quiet())
        .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert_ne!(r.status(), "error", "{:?}", r.issues);
    r
}
#[test]
fn owned_map_actual_keys_images_types_and_return_body_are_rechecked() {
    for view in ["mcParameter", "mcReturned", "mcNestedUse"] {
        let ask = format!("x=evaluate(Applications.{view},a=@v/A,b=@v/B,m=@v/m)");
        let r = map_owned_result("known", &[&ask]);
        assert_eq!(r.status(), "complete");
        assert_eq!(r.answers[0].status, Decision::Established);
    }
    // 写像の像の再検査の代表: Mapの像を書き換えると核が拒否する。
    let r = map_owned_result(
        "known",
        &["x=evaluate(Applications.mcParameter,a=@v/A,b=@v/B,m=@v/m)"],
    );
    let map = r
        .nodes
        .iter()
        .position(
            |n| matches!(&n.payload,Some(Payload::Scalar(Scalar::Map{pairs,..}))if pairs.len()==2),
        )
        .unwrap();
    rejects_mutated_prefix(&r, map, |ns| {
        let Some(Payload::Scalar(Scalar::Map { pairs, .. })) = &mut ns[map].payload else {
            panic!()
        };
        let key = pairs[0].0.clone();
        pairs[0].1 = key;
    });
}

#[test]
fn owned_map_actual_domain_roster_stop_keeps_values_refutation_and_prefix() {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Applications.mcMissingZero,p=@v/p)",
        "prior=check(Applications.prior)",
        "current=evaluate(Applications.mcObserved,a=@v/A,b=@v/B,m=@v/m,p=@v/p)",
        "later=evaluate(Applications.seed)",
    ];
    let normal = map_owned_result("stop", &asks);
    let bytes = normal.prepared.inputs().sources().law().bytes();
    let span = normal
        .prepared
        .inputs()
        .law()
        .exprs
        .iter()
        .find(|x| &bytes[x.span.0..x.span.1] == b"mcAccept(a,b,m.states)")
        .unwrap()
        .span;
    let expected = crate::result::Signal::Term;
    let armed = Rc::new(Cell::new(false));
    let traversing = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(0));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut c = Control::new(move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            Some(crate::result::Signal::Term)
        } else {
            None
        }
    });
    let prepared = prepare_observed(owned_map_fixture::input("stop", "r1"), &asks, &mut c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "prior" {
            let (a, t, s) = (armed.clone(), traversing.clone(), seen.clone());
            data::observe_iterations(move |at, ctx, operation, _| {
                if at != span {
                    return;
                }
                if ctx.request == 2 && operation == "call_arguments_complete" {
                    t.set(true);
                }
                if operation == "owned_call_map_domain_roster" && t.get() {
                    let i = s.get();
                    s.set(i + 1);
                    if i == 2 {
                        a.set(true);
                    }
                }
            });
        }
        Ok(())
    });
    data::clear_iteration_observer();
    let stopped = stopped.unwrap();
    assert_eq!(seen.get(), 3);
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(expected));
    assert_eq!(
        format!("{:?}", &stopped.answers[..2]),
        format!("{:?}", &normal.answers[..2])
    );
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert!(stopped.answers[0].reasons.iter().any(|r| {
        matches!(r.kind, ReasonKind::Missing)
            && r.missing
                .iter()
                .any(|f| f.field.as_deref() == Some("Reservations.State.free"))
    }));
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    for a in stopped.answers.iter().skip(2) {
        assert_eq!(a.status, Decision::Undetermined);
        assert!(a.outputs.is_empty());
        let reason = a
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s)if *s==expected))
            .unwrap();
        let (Json::Obj(ref actual), Json::Obj(ref wanted)) = (reason.wire(), expected.issue())
        else {
            panic!("stop")
        };
        assert_eq!(actual["details"], wanted["details"]);
        assert_eq!(reason.request, a.id);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}

#[test]
fn missing_owned_map_uses_complete_original_fibers_before_candidate_tables() {
    use std::{cell::Cell, rc::Rc};
    let input = crate::input::check_inputs(owned_map_fixture::input("missing", "r1"), &mut quiet())
        .unwrap();
    let visits = Rc::new(Cell::new(0));
    let seen = visits.clone();
    let mut c = Control::new(move |p| {
        if p == Checkpoint::FiniteIteration {
            seen.set(seen.get() + 1);
        }
        (seen.get() >= 5000).then_some(crate::result::Signal::Int)
    });
    let env = Environment::with_requests(&input, &[], &mut c).unwrap();
    let roster = Environment::with_requests(&input, &[], &mut quiet())
        .unwrap()
        .finite_values(&Type::Ref("Reservations.State".into()), &mut |_, _| {})
        .unwrap();
    assert_eq!(roster.values.len(), 8);
    let fields = [Fact {
        snapshot: "v".into(),
        subject: "m".into(),
        field: Some("Reservations.Migration.states".into()),
        atom: None,
    }];
    let mut phases = std::collections::BTreeMap::new();
    let all = env
        .completion_assignments(&fields, &mut |phase, index| {
            phases.insert(phase, index);
        })
        .unwrap();
    assert!(c.stop_reason().is_none());
    assert_eq!(phases["type_enum"], 8);
    assert_eq!(phases["reference_constraints"], 8);
    assert_eq!(all.values.len(), 4);
    let mut images = std::collections::BTreeSet::new();
    for value in &all.values {
        let Scalar::Map {
            domain,
            codomain,
            pairs,
        } = value
        else {
            panic!("Map")
        };
        assert_eq!(domain, &Type::Ref("Reservations.State".into()));
        assert_eq!(codomain, domain);
        assert_eq!(pairs.len(), 2);
        let mut targets = vec![];
        for ((key, image), expected) in pairs.iter().zip(["p", "q"]) {
            assert!(
                matches!(key,Scalar::Subject {snapshot,subject,..} if snapshot=="v" && subject==expected)
            );
            let Scalar::Subject {
                snapshot, subject, ..
            } = image
            else {
                panic!("image")
            };
            assert_eq!(snapshot, "v");
            assert!(["r", "s"].contains(&subject.as_str()));
            targets.push(subject.clone());
        }
        assert!(images.insert(targets));
    }
    assert_eq!(
        images,
        [
            vec!["r".to_string(), "r".into()],
            vec!["r".into(), "s".into()],
            vec!["s".into(), "r".into()],
            vec!["s".into(), "s".into()]
        ]
        .into_iter()
        .collect()
    );
    for snapshot in ["v", "w"] {
        assert!(all.scope.snapshots.contains(snapshot));
        for atom in ["p-owner", "q-owner", "r-owner", "s-owner", "m-from", "m-to"] {
            assert!(
                all.support
                    .iter()
                    .any(|f| f.snapshot == snapshot && f.atom.as_deref() == Some(atom))
            );
        }
    }
}
