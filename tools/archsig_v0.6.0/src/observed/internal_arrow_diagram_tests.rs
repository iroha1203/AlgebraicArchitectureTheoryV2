use super::*;
use crate::observed::{
    PreparedObserved, architecture_result,
    control::{Limits, Usage},
    input::{InputSources, check_inputs},
    request::resolve_native_for_test,
};
use std::{cell::Cell, rc::Rc};
const DEF: &[u8] = include_bytes!("../../tests/fixtures/internal-arrow.atoms.json");
const LAW: &str = include_str!("../../tests/fixtures/internal-arrow.law");
const MAP: &str = include_str!("../../tests/fixtures/internal-arrow.archmap.json");
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn prepared(map: &str, asks: &[&str]) -> PreparedObserved {
    let defs = crate::definition::check_definitions(&[("definition0", DEF)]).unwrap();
    let digest = &defs.vocabularies["Flow"].digest;
    let input = InputSources::from_bytes(
        vec![DEF.to_vec()],
        LAW.replace("@FLOW_DIGEST@", digest).into_bytes(),
        map.replace("@FLOW_DIGEST@", digest).into_bytes(),
    );
    let inputs =
        Arc::new(check_inputs(input, &mut quiet()).unwrap_or_else(|e| panic!("{:?}", e.issues())));
    let requests =
        resolve_native_for_test(inputs.law(), inputs.archmap(), asks, &mut quiet()).unwrap();
    PreparedObserved {
        inputs,
        requests,
        object: None,
    }
}
fn empty(p: &PreparedObserved) -> Graph {
    let mut g = Graph::new(&quiet());
    g.requests = p.requests().requests().to_vec();
    g
}
fn build(p: &PreparedObserved, g: &mut Graph) -> architecture_result::Architecture {
    let mut c = quiet();
    let env = Environment::with_prepared(p, &mut c).unwrap();
    architecture_result::build(
        p.shared_inputs(),
        &env,
        g,
        &p.requests().requests()[g.active.request],
        &mut c,
    )
    .unwrap()
}
fn family(p: &PreparedObserved, g: &mut Graph, a: &architecture_result::Architecture) -> Objects {
    objects::retain(g, p.shared_inputs(), a.reference, &mut quiet())
        .unwrap()
        .unwrap()
}
fn replay(
    p: &PreparedObserved,
    original: &Graph,
    nodes: &[Node],
) -> Result<Graph, ValidationFailure> {
    let mut c = quiet();
    let env = Environment::with_prepared(p, &mut c)?;
    let mut g = empty(p);
    g.requests = original.requests.clone();
    for (i, n) in nodes.iter().enumerate() {
        g.active = original.contexts[i];
        env.validate(&g, n)?;
        g.push(n.clone())?;
    }
    Ok(g)
}
fn data(g: &Graph, r: NodeRef) -> &Data {
    let Some(Payload::Construction(v)) = &g.nodes[r.0].payload else {
        panic!("native")
    };
    let D::InternalArrows(d) = &v.data else {
        panic!("internal")
    };
    d
}
fn scalar(g: &Graph, r: NodeRef) -> &str {
    let Scalar::Subject { subject, .. } = g.scalar(r).unwrap() else {
        panic!("subject")
    };
    subject
}
fn fact(id: &str, field: Option<&str>) -> Fact {
    let ty = match id {
        "A" | "B" => "Root",
        "p" | "q" | "r" => "Node",
        "e" | "f" | "g" => "Step",
        "x" | "y" => "External",
        _ => panic!("id"),
    };
    Fact {
        snapshot: "v".into(),
        subject: id.into(),
        field: field.map(|f| format!("Flow.{ty}.{f}")),
        atom: field.map(|f| format!("{id}-{f}")),
    }
}
fn remove(map: &str, id: &str) -> String {
    map.lines()
        .filter(|l| !l.contains(&format!("\"id\":\"{id}\"")))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]")
}
fn edit(map: &str, id: &str, before: &str, after: &str) -> String {
    let mut hits = 0;
    let r = map
        .lines()
        .map(|l| {
            if l.contains(&format!("\"id\":\"{id}\"")) {
                assert!(l.contains(before));
                hits += 1;
                l.replace(before, after)
            } else {
                l.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    assert_eq!(hits, 1);
    r
}
#[test]
fn generators_use_actual_owned_architectures_and_total_actions_with_fixed_complements() {
    let p = prepared(MAP, &["b=build(FlowRead,on=@v/A)"]);
    let mut g = empty(&p);
    let a = build(&p, &mut g);
    let o = family(&p, &mut g, &a);
    let start = g.nodes.len();
    let d = retain(
        &mut g,
        p.shared_inputs(),
        a.reference,
        &o,
        a.universe,
        &mut quiet(),
    )
    .unwrap();
    assert!(d.all_preserved);
    assert_eq!(d.rows.len(), 2);
    assert_eq!(o.architectures.len(), 3);
    for (row, name, from, to) in [(&d.rows[0], "e", "p", "q"), (&d.rows[1], "f", "q", "p")] {
        assert_eq!(scalar(&g, row.subject), name);
        assert!(row.missing.is_empty());
        assert!(row.evidence.is_empty());
        let Part::Operation {
            subject,
            source,
            target,
            candidate,
            map,
            action,
        } = data(&g, row.operation.unwrap()).part()
        else {
            panic!("op")
        };
        assert_eq!(*subject, row.subject);
        assert_eq!(Some(*candidate), row.candidate);
        let from_index = if from == "p" { 1 } else { 2 };
        let to_index = if to == "q" { 2 } else { 1 };
        assert_eq!(*source, o.architectures[from_index]);
        assert_eq!(*target, o.architectures[to_index]);
        assert_ne!(source, target);
        assert!(matches!(data(&g,*map).part(),Part::Map{candidate:c} if c==candidate));
        assert!(
            matches!(data(&g,*candidate).part(),Part::Candidate{declaration,subject:s,source:x,target:y,action:z} if declaration=="Flow.Step"&&s==subject&&x==source&&y==target&&z==action)
        );
        let Part::Action { universe, images } = data(&g, *action).part() else {
            panic!("action")
        };
        assert_eq!(*universe, a.universe);
        let u = a.witness.construction().universe();
        assert_eq!(u.len(), 45);
        assert_eq!(images.len(), 45);
        for (atom, image) in u.iter().zip(images) {
            let fields = [
                None,
                Some("owner"),
                Some("quantity"),
                Some("links"),
                Some("pair"),
                Some("choice"),
                Some("tagged"),
                Some("lookup"),
                Some("members"),
            ];
            let moved = fields
                .iter()
                .find(|f| *atom == fact(from, **f))
                .map(|f| fact(to, *f));
            assert_eq!(image, moved.as_ref().unwrap_or(atom));
        }
        assert_eq!(
            data(&g, row.operation.unwrap()).wire(),
            Json::obj([
                ("source", source.wire()),
                ("target", target.wire()),
                ("candidate", candidate.wire()),
                ("configuration_map", map.wire()),
                ("action", action.wire()),
                (
                    "name",
                    Json::obj([
                        ("kind", Json::str("generator")),
                        ("subject", subject.wire())
                    ])
                ),
                ("word", refs(&[*subject]))
            ])
        );
    }
    for (i, n) in g.nodes.iter().enumerate().skip(start) {
        assert!(n.arguments.iter().all(|r| r.0 < i));
        assert_eq!(n.scope, g.get(a.reference).unwrap().scope);
        assert!(n.support.contains(&fact("x", Some("quantity"))));
    }
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn refuted_arrows_keep_candidates_and_original_counterexample_facts_without_operations() {
    let bad = edit(
        MAP,
        "q-links",
        r#"[["v","q"],["v","r"],["v","q"]]"#,
        r#"[["v","r"],["v","q"],["v","q"]]"#,
    );
    let p = prepared(&bad, &["b=build(FlowRead,on=@v/A)"]);
    let mut g = empty(&p);
    let a = build(&p, &mut g);
    let o = family(&p, &mut g, &a);
    let d = retain(
        &mut g,
        p.shared_inputs(),
        a.reference,
        &o,
        a.universe,
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(d.rows.len(), 2);
    assert!(!d.all_preserved);
    for row in &d.rows {
        assert!(row.candidate.is_some());
        assert!(row.operation.is_none());
        assert!(!row.evidence.is_empty());
        assert!(row.missing.is_empty());
    }
    let row = &d.rows[0];
    assert!(row.evidence.iter().any(|r|matches!(data(&g,*r).part(),Part::Evidence{subject,left,right,facts} if *subject==row.subject&&*left==o.architectures[1]&&*right==o.architectures[2]&&facts==&vec![fact("p",Some("links")),fact("q",Some("links"))])));
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn missing_membership_keeps_original_partial_architecture_and_does_not_make_operations() {
    let p = prepared(&remove(MAP, "g-owner"), &["b=build(FlowRead,on=@v/A)"]);
    let mut g = empty(&p);
    let a = build(&p, &mut g);
    let before = g.nodes.clone();
    assert!(!a.complete);
    assert!(objects::retain(&mut g, p.shared_inputs(), a.reference, &mut quiet()).is_err());
    assert_eq!(g.nodes, before);
    assert!(a.reasons.iter().any(|r| {
        r.missing
            .iter()
            .any(|f| f.subject == "g" && f.field.as_deref() == Some("Flow.Step.owner"))
    }));
    assert!(
        !g.nodes
            .iter()
            .any(|n| n.ty == NodeType::Construction(T::Operation))
    );
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn no_arrows_is_a_complete_empty_generator_family() {
    let p = prepared(MAP, &["b=build(FlowRead,on=@v/x)"]); // External has no owner and no owned arrow type.
    let mut g = empty(&p);
    let a = build(&p, &mut g);
    let o = family(&p, &mut g, &a);
    let before = g.nodes.clone();
    let d = retain(
        &mut g,
        p.shared_inputs(),
        a.reference,
        &o,
        a.universe,
        &mut quiet(),
    )
    .unwrap();
    assert!(d.all_preserved);
    assert!(d.rows.is_empty());
    assert_eq!(g.nodes, before);
}
#[test]
fn changed_inputs_requests_plans_metadata_and_edges_are_rejected() {
    let p = prepared(MAP, &["b=build(FlowRead,on=@v/A)"]);
    let mut g = empty(&p);
    let a = build(&p, &mut g);
    let o = family(&p, &mut g, &a);
    let d = retain(
        &mut g,
        p.shared_inputs(),
        a.reference,
        &o,
        a.universe,
        &mut quiet(),
    )
    .unwrap();
    let r = d.rows[0].operation.unwrap();
    for mode in 0..7 {
        let mut nodes = g.nodes.clone();
        match mode {
            0 => nodes[r.0].arguments.swap(3, 4),
            1 => nodes[r.0].support.clear(),
            2 => nodes[r.0].scope = Scope::default(),
            3 => {
                let Some(Payload::Construction(v)) = &mut nodes[r.0].payload else {
                    panic!("payload")
                };
                let D::InternalArrows(x) = &mut v.data else {
                    panic!("data")
                };
                let mut source = (*x.source).clone();
                let Part::Operation { source: s, .. } = &mut source.parts[x.index] else {
                    panic!("op")
                };
                *s = o.architectures[2];
                x.source = Arc::new(source);
            }
            4 => {
                let Some(Payload::Construction(v)) = &mut nodes[r.0].payload else {
                    panic!("payload")
                };
                let D::InternalArrows(x) = &mut v.data else {
                    panic!("data")
                };
                x.index += 1;
            }
            5 => {
                let Some(Payload::Construction(v)) = &mut nodes[r.0].payload else {
                    panic!("payload")
                };
                let D::InternalArrows(x) = &mut v.data else {
                    panic!("data")
                };
                let mut source = (*x.source).clone();
                source.outputs.all_preserved = false;
                x.source = Arc::new(source);
            }
            _ => nodes[r.0].arguments.push(NodeRef(r.0)),
        }
        assert!(replay(&p, &g, &nodes).is_err(), "mode {mode}");
    }
    let changed = prepared(
        &edit(MAP, "q-quantity", r#""7""#, r#""8""#),
        &["b=build(FlowRead,on=@v/A)"],
    );
    assert!(replay(&changed, &g, &g.nodes).is_err());
    let mut foreign = empty(&p);
    foreign.requests = g.requests.clone();
    foreign.requests[0].head = crate::observed::request::Selector::Declaration {
        name: "OtherRead".into(),
    };
    foreign.contexts = g.contexts.clone();
    assert!(replay(&p, &foreign, &g.nodes).is_err());
}
#[test]
fn all_stop_reasons_keep_exact_completed_prefix_and_never_publish_unfinished_generators() {
    let p = prepared(MAP, &["b=build(FlowRead,on=@v/A)"]);
    let measured = Rc::new(Cell::new(0));
    let measured_count = measured.clone();
    let armed_measurement = Rc::new(Cell::new(false));
    let active_measurement = armed_measurement.clone();
    let mut measure = Control::new(Limits::default(), move |point| {
        if active_measurement.get() && point == Checkpoint::NativeResultNode {
            measured_count.set(measured_count.get() + 1);
        }
        Usage::default()
    });
    let mut normal = Graph::new(&measure);
    normal.requests = p.requests().requests().to_vec();
    let a = build(&p, &mut normal);
    let o = family(&p, &mut normal, &a);
    let start = normal.nodes.len();
    armed_measurement.set(true);
    let diagram = retain(
        &mut normal,
        p.shared_inputs(),
        a.reference,
        &o,
        a.universe,
        &mut measure,
    )
    .unwrap();
    let total = measured.get();
    assert!(total > 2);
    let last_operation = diagram.rows.last().unwrap().operation.unwrap();
    assert_eq!(last_operation.0 + 1, normal.nodes.len());
    for mode in 0..4 {
        for (at, final_tick) in [
            (1, false),
            (total / 2, false),
            (total, false),
            (total, true),
        ] {
            let seen = Rc::new(Cell::new(0));
            let count = seen.clone();
            let armed = Rc::new(Cell::new(false));
            let active = armed.clone();
            let limits = Limits {
                time_ms: (mode == 0).then_some(1),
                memory_mib: (mode == 1).then_some(1),
            };
            let mut c = Control::new(limits, move |point| {
                if active.get() && point == Checkpoint::NativeResultNode {
                    count.set(count.get() + 1);
                }
                if count.get() < at || (final_tick && point != Checkpoint::InternalArrow) {
                    return Usage::default();
                }
                Usage {
                    elapsed_ms: if mode == 0 { 1 } else { 0 },
                    memory_mib: if mode == 1 { 1 } else { 0 },
                    signal: match mode {
                        2 => Some(crate::result::Signal::Int),
                        3 => Some(crate::result::Signal::Term),
                        _ => None,
                    },
                }
            });
            let mut g = Graph::new(&c);
            g.requests = p.requests().requests().to_vec();
            let a = build(&p, &mut g);
            let o = family(&p, &mut g, &a);
            let prefix = g.nodes.clone();
            armed.set(true);
            assert!(matches!(
                retain(
                    &mut g,
                    p.shared_inputs(),
                    a.reference,
                    &o,
                    a.universe,
                    &mut c
                ),
                Err(ValidationFailure::Stop(_))
            ));
            assert!(c.stop_reason().is_some());
            assert_eq!(&g.nodes[..start], prefix);
            assert!(g.nodes.len() <= normal.nodes.len());
            if at == total {
                assert_eq!(g.nodes.len(), normal.nodes.len());
                assert_eq!(
                    g.get(last_operation).unwrap().ty,
                    NodeType::Construction(T::Operation)
                );
            }
            for (actual, expected) in g
                .nodes
                .iter()
                .skip(start)
                .zip(normal.nodes.iter().skip(start))
            {
                assert_eq!(actual.ty, expected.ty);
                assert_eq!(actual.arguments, expected.arguments);
                assert_eq!(actual.support, expected.support);
                assert_eq!(actual.scope, expected.scope);
                let Some(Payload::Construction(av)) = &actual.payload else {
                    panic!("actual")
                };
                let Some(Payload::Construction(ev)) = &expected.payload else {
                    panic!("expected")
                };
                assert_eq!(av.wire(), ev.wire());
            }
            replay(&p, &g, &g.nodes).unwrap();
        }
    }
}

#[test]
fn equal_observed_quantities_and_refuted_required_laws_do_not_change_generator_endpoints() {
    let map = edit(MAP, "q-quantity", r#""7""#, r#""2""#);
    let mut p = prepared(&map, &["b=build(FlowRead,on=@v/A)"]);
    let sources = p.shared_inputs().sources().clone();
    let law = String::from_utf8(sources.law().bytes().to_vec())
        .unwrap()
        .replace(
            "view amount",
            "law required zero(n:Node):n.quantity=0; view amount",
        );
    let inputs = Arc::new(
        check_inputs(
            InputSources::from_bytes(
                vec![DEF.to_vec()],
                law.into_bytes(),
                sources.archmap().bytes().to_vec(),
            ),
            &mut quiet(),
        )
        .unwrap(),
    );
    p.inputs = inputs;
    let mut g = empty(&p);
    let a = build(&p, &mut g);
    let o = family(&p, &mut g, &a);
    assert_ne!(o.architectures[1], o.architectures[2]);
    let d = retain(
        &mut g,
        p.shared_inputs(),
        a.reference,
        &o,
        a.universe,
        &mut quiet(),
    )
    .unwrap();
    assert!(d.all_preserved);
    assert_eq!(d.rows.len(), 2);
    let Part::Operation { source, target, .. } = data(&g, d.rows[0].operation.unwrap()).part()
    else {
        panic!("op")
    };
    assert_eq!((*source, *target), (o.architectures[1], o.architectures[2]));
    let instance = a
        .witness
        .readings()
        .instances()
        .iter()
        .position(|r| {
            r.declaration().name == "FlowRead.zero"
                && r.bindings().iter().any(|b| b.subject().subject == "p")
        })
        .unwrap();
    let evaluated = crate::observed::object_evaluate::evaluate_object_instance(
        p.shared_inputs(),
        a.witness.readings(),
        1,
        instance,
        &mut quiet(),
    )
    .unwrap();
    let crate::observed::object_evaluate::ObjectEvaluationOutcome::Evaluated(result) =
        evaluated.outcome()
    else {
        panic!("evaluated Law")
    };
    assert_eq!(result.answers[0].status, Decision::Refuted);
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn original_producers_recheck_under_another_request_and_foreign_object_tables_are_rejected() {
    let p = prepared(
        MAP,
        &["a=build(FlowRead,on=@v/A)", "b=build(OtherRead,on=@v/A)"],
    );
    let mut g = empty(&p);
    let a = build(&p, &mut g);
    let oa = family(&p, &mut g, &a);
    let da = retain(
        &mut g,
        p.shared_inputs(),
        a.reference,
        &oa,
        a.universe,
        &mut quiet(),
    )
    .unwrap();
    g.active.request = 1;
    let b = build(&p, &mut g);
    let ob = family(&p, &mut g, &b);
    let before = g.nodes.clone();
    assert!(
        retain(
            &mut g,
            p.shared_inputs(),
            b.reference,
            &oa,
            b.universe,
            &mut quiet()
        )
        .is_err()
    );
    assert_eq!(g.nodes, before);
    let db = retain(
        &mut g,
        p.shared_inputs(),
        b.reference,
        &ob,
        b.universe,
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(da.rows.len(), 2);
    assert_eq!(db.rows.len(), 2);
    assert_ne!(da.rows[0].operation, db.rows[0].operation);
    let mut c = quiet();
    let env = Environment::with_prepared(&p, &mut c).unwrap();
    let old = da.rows[0].operation.unwrap();
    env.recheck_node(&g, &g.get(old).unwrap().clone(), old.0)
        .unwrap();
    replay(&p, &g, &g.nodes).unwrap();
    let before = g.nodes.clone();
    assert!(
        retain(
            &mut g,
            p.shared_inputs(),
            a.reference,
            &oa,
            a.universe,
            &mut quiet()
        )
        .is_err()
    );
    assert_eq!(g.nodes, before);
}
#[test]
fn kernel_and_planning_stops_leave_all_existing_objects_unchanged() {
    let p = prepared(MAP, &["b=build(FlowRead,on=@v/A)"]);
    for checkpoint in [
        Checkpoint::InternalArrowRoster,
        Checkpoint::InternalArrowRow,
        Checkpoint::ConfigurationOperation,
    ] {
        let mut c = Control::new(Limits::default(), move |point| Usage {
            signal: (point == checkpoint).then_some(crate::result::Signal::Int),
            ..Usage::default()
        });
        let mut g = empty(&p);
        let a = build(&p, &mut g);
        let o = family(&p, &mut g, &a);
        let before = g.nodes.clone();
        assert!(matches!(
            retain(
                &mut g,
                p.shared_inputs(),
                a.reference,
                &o,
                a.universe,
                &mut c
            ),
            Err(ValidationFailure::Stop(_))
        ));
        assert_eq!(g.nodes, before);
        replay(&p, &g, &g.nodes).unwrap();
    }
}

#[test]
fn a_missing_target_field_keeps_the_arrow_and_slot_without_fabricating_a_candidate() {
    let p = prepared(&remove(MAP, "q-quantity"), &["b=build(FlowRead,on=@v/A)"]);
    let mut g = empty(&p);
    let a = build(&p, &mut g);
    assert!(a.complete);
    let o = family(&p, &mut g, &a);
    let d = retain(
        &mut g,
        p.shared_inputs(),
        a.reference,
        &o,
        a.universe,
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(d.rows.len(), 2);
    assert!(!d.all_preserved);
    let row = &d.rows[0];
    assert_eq!(scalar(&g, row.subject), "e");
    assert!(row.candidate.is_none());
    assert!(row.operation.is_none());
    assert_eq!(
        row.missing,
        vec![Fact {
            snapshot: "v".into(),
            subject: "q".into(),
            field: Some("Flow.Node.quantity".into()),
            atom: None
        }]
    );
    assert!(row.evidence.is_empty());
    assert_eq!(scalar(&g, d.rows[1].subject), "f");
    assert!(d.rows[1].operation.is_some());
    replay(&p, &g, &g.nodes).unwrap();
}

#[test]
fn shared_universe_keeps_external_snapshot_and_mode_in_every_generated_scope() {
    let mut map=MAP.replace("  \"origins\": [",r#"  "origins": [{"id":"proposal","mode":"proposed","method":"独立した原始値。","locations":[],"note":"候補。"},"#);
    assert!(map.contains("\n}]\n}"));
    map=map.replace("\n}]\n}",r#"
},{"id":"w","origin":"proposal","subjects":[{"id":"z","type":"Flow.Root","origin":"proposal"}],"atoms":[]}]
}"#);
    let p = prepared(&map, &["b=build(FlowRead,on=@v/A)"]);
    let mut g = empty(&p);
    let a = build(&p, &mut g);
    let o = family(&p, &mut g, &a);
    assert!(!g.get(a.reference).unwrap().scope.snapshots.contains("w"));
    assert!(!g.get(a.reference).unwrap().scope.modes.contains("proposed"));
    assert!(g.get(a.universe).unwrap().scope.snapshots.contains("w"));
    assert!(g.get(a.universe).unwrap().scope.modes.contains("proposed"));
    let start = g.nodes.len();
    let d = retain(
        &mut g,
        p.shared_inputs(),
        a.reference,
        &o,
        a.universe,
        &mut quiet(),
    )
    .unwrap();
    assert!(d.all_preserved);
    let existence = Fact {
        snapshot: "w".into(),
        subject: "z".into(),
        field: None,
        atom: None,
    };
    let quantity = fact("x", Some("quantity"));
    for node in &g.nodes[start..] {
        assert!(node.scope.snapshots.contains("w"));
        assert!(node.scope.modes.contains("proposed"));
        assert!(node.support.contains(&existence));
        assert!(node.support.contains(&quantity));
    }
    for row in &d.rows {
        let Part::Operation { action, .. } = data(&g, row.operation.unwrap()).part() else {
            panic!("op")
        };
        let Part::Action { images, .. } = data(&g, *action).part() else {
            panic!("action")
        };
        assert_eq!(images.len(), 46);
        for f in [&existence, &quantity] {
            let index = a
                .witness
                .construction()
                .universe()
                .iter()
                .position(|v| v == f)
                .unwrap();
            assert_eq!(&images[index], f);
        }
    }
    replay(&p, &g, &g.nodes).unwrap();
    let mut changed = g.nodes.clone();
    changed[d.rows[0].operation.unwrap().0]
        .scope
        .modes
        .remove("proposed");
    assert!(replay(&p, &g, &changed).is_err());
}

#[test]
fn unfinished_object_family_prefixes_are_rejected_before_appending_any_arrow_nodes() {
    let p = prepared(MAP, &["b=build(FlowRead,on=@v/A)"]);
    for phase in 0..3 {
        let mut g = empty(&p);
        let a = build(&p, &mut g);
        let o = family(&p, &mut g, &a);
        let cut = match phase {
            0 => o.base.0 + 1,
            1 => o.objects.last().unwrap().0,
            _ => g.nodes.len() - 1,
        };
        g.nodes.truncate(cut);
        g.contexts.truncate(cut);
        let before = g.nodes.clone();
        let contexts = g.contexts.clone();
        replay(&p, &g, &g.nodes).unwrap();
        assert!(
            objects::original_family(&g, o.base).is_err(),
            "unfinished phase {phase}"
        );
        assert!(
            retain(
                &mut g,
                p.shared_inputs(),
                a.reference,
                &o,
                a.universe,
                &mut quiet()
            )
            .is_err()
        );
        assert_eq!(g.nodes, before);
        assert_eq!(g.contexts, contexts);
        replay(&p, &g, &g.nodes).unwrap();
    }
}
#[test]
fn replaced_object_components_readings_and_foreign_contexts_are_rejected_before_generation() {
    let p = prepared(
        MAP,
        &["b=build(FlowRead,on=@v/A)", "idle=build(OtherRead,on=@v/A)"],
    );
    for mode in 0..4 {
        let mut g = empty(&p);
        let a = build(&p, &mut g);
        let o = family(&p, &mut g, &a);
        let last = g.nodes.len() - 1;
        match mode {
            0 => g.nodes[o.objects.last().unwrap().0] = g.nodes[a.root.0].clone(),
            1 => g.nodes[last].scope.readings.clear(),
            2 => {
                g.contexts.pop();
            }
            _ => g.contexts[last].request = 1,
        }
        let before = g.nodes.clone();
        let contexts = g.contexts.clone();
        assert!(
            objects::original_family(&g, o.base).is_err(),
            "corrupt mode {mode}"
        );
        assert!(
            retain(
                &mut g,
                p.shared_inputs(),
                a.reference,
                &o,
                a.universe,
                &mut quiet()
            )
            .is_err()
        );
        assert_eq!(g.nodes, before);
        assert_eq!(g.contexts, contexts);
    }
}
