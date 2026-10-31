use super::*;
mod owned_map_fixture {
    use crate as archsig;
    include!("../../tests/common/owned_map_calls.rs");
}
fn map_owned_result(mode: &str, asks: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        owned_map_fixture::input(mode, "r1"),
        asks,
        &mut named_call_quiet(),
    )
    .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert_ne!(r.status(), "error", "{:?}", r.issues);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
#[test]
fn owned_map_actual_keys_images_types_and_return_body_are_rechecked() {
    for view in ["mcParameter", "mcReturned", "mcNestedUse"] {
        let ask = format!("x=evaluate(Applications.{view},a=@v/A,b=@v/B,m=@v/m)");
        let r = map_owned_result("known", &[&ask]);
        assert_eq!(r.status(), "complete");
        let map = r
            .nodes
            .iter()
            .enumerate()
            .find_map(|(i, n)| {
                matches!(&n.payload,Some(Payload::Scalar(Scalar::Map{pairs,..}))if pairs.len()==2)
                    .then_some(i)
            })
            .unwrap();
        completion_mutation(&r, map, |ns| {
            let Some(Payload::Scalar(Scalar::Map { pairs, .. })) = &mut ns[map].payload else {
                panic!()
            };
            pairs.pop();
        });
        completion_mutation(&r, map, |ns| {
            let Some(Payload::Scalar(Scalar::Map { pairs, .. })) = &mut ns[map].payload else {
                panic!()
            };
            let image = pairs[0].1.clone();
            pairs[0].0 = image;
        });
        completion_mutation(&r, map, |ns| {
            let Some(Payload::Scalar(Scalar::Map { pairs, .. })) = &mut ns[map].payload else {
                panic!()
            };
            let key = pairs[0].0.clone();
            pairs[0].1 = key;
        });
        completion_mutation(&r, map, |ns| {
            let Some(Payload::Scalar(Scalar::Map { domain, .. })) = &mut ns[map].payload else {
                panic!()
            };
            *domain = Type::Ref("Reservations.System".into());
        });
        completion_mutation(&r, map, |ns| ns[map].support.clear());
        completion_mutation(&r, map, |ns| ns[map].scope.snapshots.clear());
        if view == "mcReturned" {
            let bytes = r.prepared.inputs().sources().law().bytes();
            let source = r
                .nodes
                .iter()
                .enumerate()
                .find_map(|(i, n)| match &n.payload {
                    Some(Payload::Expression {
                        location: Location::Law { span },
                        ..
                    }) if &bytes[span.0..span.1] == b"mcReturn(a,b,m.states)" => Some(NodeRef(i)),
                    _ => None,
                })
                .unwrap();
            let frame = r.frames.iter().position(|f| f.source == source).unwrap();
            let body = r
                .nodes
                .iter()
                .enumerate()
                .find_map(|(i, n)| {
                    (r.contexts[i].frame == Some(frame)
                        && matches!(n.payload, Some(Payload::Evaluation { .. })))
                    .then_some(i)
                })
                .unwrap();
            completion_mutation(&r, body, |ns| {
                let Some(Payload::Evaluation { value, .. }) = &mut ns[body].payload else {
                    panic!()
                };
                assert!(value.is_some());
                *value = None;
            });
        }
    }
}
#[test]
fn owned_map_expected_domain_sets_recheck_original_complete_roster_after_shape_acceptance() {
    let r = map_owned_result(
        "empty",
        &["x=evaluate(Applications.mcParameter,a=@v/A,b=@v/B,m=@v/m)"],
    );
    let target = owned_condition(&r, 0);
    let edges = r.nodes[target].arguments.clone();
    let n = edges.len();
    let required = edges[n - 2];
    let actual = edges[n - 3];
    let proof = edges[n - 1];
    let Some(Payload::Scalar(Scalar::Set { items, .. })) = &r.nodes[required.0].payload else {
        panic!()
    };
    assert_eq!(items.len(), 2);
    assert!(
        matches!(&r.nodes[actual.0].payload,Some(Payload::Scalar(Scalar::Set{items,..}))if items.is_empty())
    );
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let env = Environment::new(r.prepared.inputs(), &mut named_call_quiet()).unwrap();
    env.recheck_node(&g, &g.nodes[target], target).unwrap();
    let old = g.nodes[required.0].clone();
    let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut g.nodes[required.0].payload else {
        panic!()
    };
    items.pop();
    assert!(
        g.owned_call_counterexample_shape(&g.nodes[proof.0])
            .unwrap()
    );
    g.validate_proposition_evidence(&g.nodes[target]).unwrap();
    assert!(matches!(
        env.recheck_node(&g, &g.nodes[target], target),
        Err(ValidationFailure::Internal(_))
    ));
    g.nodes[required.0] = old;
    env.recheck_node(&g, &g.nodes[target], target).unwrap();
    completion_mutation(&r, required.0, |ns| {
        let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut ns[required.0].payload else {
            panic!()
        };
        items.pop();
    });
    completion_mutation(&r, required.0, |ns| ns[required.0].support.clear());
    completion_mutation(&r, proof.0, |ns| {
        ns[proof.0].ty = NodeType::Value(Type::Bool)
    });
    completion_mutation(&r, target, |ns| ns[target].scope.snapshots.clear());
    completion_mutation(&r, target, |ns| ns[target].support.clear());
}
#[test]
fn owned_map_equal_foreign_producers_and_success_session_cannot_authorize_changed_proofs() {
    for (mode, args) in [("empty", "a=@v/A,b=@v/B"), ("known", "a=@v/A,b=@v/A")] {
        let a = format!("first=evaluate(Applications.mcParameter,{args},m=@v/m)");
        let b = a.replacen("first=", "second=", 1);
        let r = map_owned_result(mode, &[&a, &b]);
        let donor = owned_condition(&r, 0);
        let target = owned_condition(&r, 1);
        let own = r.nodes[target].arguments.clone();
        let other = r.nodes[donor].arguments.clone();
        let n = own.len();
        assert_ne!(own[3], other[3]);
        let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
        let env = Environment::new(r.prepared.inputs(), &mut named_call_quiet()).unwrap();
        assert_eq!(
            env.owned_call_argument(&g, own[3]).unwrap(),
            env.owned_call_argument(&g, other[3]).unwrap()
        );
        completion_mutation(&r, target, |ns| {
            for p in [own[n - 3], own[n - 2], own[n - 1], NodeRef(target)] {
                ns[p.0].arguments[3] = other[3];
            }
        });
        let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
        env.recheck_node(&g, &g.nodes[target], target).unwrap();
        let old = g.nodes[target].support.clone();
        g.nodes[target].support.clear();
        assert!(!old.is_empty());
        assert!(matches!(
            env.recheck_node(&g, &g.nodes[target], target),
            Err(ValidationFailure::Internal(_))
        ));
        g.nodes[target].support = old;
        env.recheck_node(&g, &g.nodes[target], target).unwrap();
    }
}

fn owned_map_member_stop(recheck: bool) {
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
    let (limits, usage, expected) = reservations_private_stop_usage(if recheck { 2 } else { 0 });
    let armed = Rc::new(Cell::new(false));
    let phase = Rc::new(Cell::new(false));
    let traversing = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(0));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut c = Control::new(limits, move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            usage
        } else {
            Default::default()
        }
    });
    let prepared = prepare_observed(owned_map_fixture::input("stop", "r1"), &asks, &mut c).unwrap();
    let mut cc = c.clone();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "prior" {
            let (a, ph, t, s) = (
                armed.clone(),
                phase.clone(),
                traversing.clone(),
                seen.clone(),
            );
            data::observe_iterations(move |at, ctx, operation, _| {
                if at != span {
                    return;
                }
                if !recheck && ctx.request == 2 && operation == "call_arguments_complete" {
                    t.set(true);
                }
                if operation == "owned_call_map_domain_roster"
                    && (if recheck {
                        ph.get() && ctx.request == 2
                    } else {
                        t.get()
                    })
                {
                    let i = s.get();
                    s.set(i + 1);
                    if i == 2 {
                        a.set(true);
                    }
                }
            });
        }
        if request.id == "current" && recheck {
            let fresh = Environment::new(normal.prepared.inputs(), &mut cc)?;
            phase.set(true);
            let result = fresh.validate_answer(g, request, answer);
            phase.set(false);
            result?;
        }
        Ok(())
    });
    data::clear_iteration_observer();
    let stopped = stopped.unwrap();
    assert_eq!(seen.get(), 3);
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(expected.clone()));
    assert_eq!(Some(probes.get()), frozen.get());
    assert_eq!(
        format!("{:?}", stopped.nodes),
        format!("{:?}", &normal.nodes[..stopped.nodes.len()])
    );
    assert_eq!(stopped.contexts, &normal.contexts[..stopped.contexts.len()]);
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
    for (i, a) in stopped.answers.iter().enumerate().skip(2) {
        if recheck && i == 2 {
            // 欠測のobserved回答はcomplete_answerで独立検査済み。
            assert_eq!(a.status, normal.answers[i].status);
            assert_eq!(a.status, Decision::Established);
            assert_eq!(a.outputs, normal.answers[i].outputs);
            assert_eq!(a.claim, normal.answers[i].claim);
            assert_eq!(a.evidence, normal.answers[i].evidence);
        } else {
            assert_eq!(a.status, Decision::Undetermined);
            assert!(a.outputs.is_empty());
        }
        let reason = a
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s)if *s==expected))
            .unwrap();
        let (Json::Obj(ref actual), Json::Obj(ref wanted)) = (reason.wire(), expected.wire())
        else {
            panic!("stop")
        };
        assert_eq!(actual["details"], wanted["details"]);
        assert_eq!(reason.request, a.id);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn owned_map_actual_domain_roster_stop_keeps_values_refutation_and_prefix() {
    owned_map_member_stop(false)
}
#[test]
fn owned_map_original_domain_roster_recheck_stop_keeps_verified_outputs_and_prefix() {
    owned_map_member_stop(true)
}

#[test]
fn missing_owned_map_uses_complete_original_fibers_before_candidate_tables() {
    use crate::control::{Limits, Usage};
    use std::{cell::Cell, rc::Rc};
    let input = crate::input::check_inputs(
        owned_map_fixture::input("missing", "r1"),
        &mut named_call_quiet(),
    )
    .unwrap();
    let visits = Rc::new(Cell::new(0));
    let seen = visits.clone();
    let mut c = Control::new(Limits::default(), move |p| {
        if p == Checkpoint::FiniteIteration {
            seen.set(seen.get() + 1);
        }
        Usage {
            signal: (seen.get() >= 5000).then_some(crate::result::Signal::Int),
            ..Usage::default()
        }
    });
    let env = Environment::with_requests(&input, &[], &mut c).unwrap();
    let roster = Environment::with_requests(&input, &[], &mut named_call_quiet())
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
