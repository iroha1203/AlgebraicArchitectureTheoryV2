use super::*;
use crate::observed::{PreparedObserved, request::resolve_native_for_test};
use std::collections::BTreeSet;
const DEFINITION: &[u8] =
    include_bytes!("../../../tests/fixtures/configuration-profile.atoms.json");
const LAW: &str = include_str!("../../../tests/fixtures/configuration-profile.law");
const MAP: &str = include_str!("../../../tests/fixtures/configuration-profile.archmap.json");
use crate::control::quiet;
fn inputs(map: &str) -> Arc<CheckedInputs> {
    let defs = crate::definition::check_definitions(&[("definition0", DEFINITION)]).unwrap();
    let digest = &defs.vocabularies()["Profile"].digest;
    Arc::new(
        crate::input::check_inputs(
            crate::input::InputSources::from_bytes(
                vec![DEFINITION.to_vec()],
                LAW.replace("@PROFILE_DIGEST@", digest).into_bytes(),
                map.replace("@PROFILE_DIGEST@", digest).into_bytes(),
            ),
            &mut quiet(),
        )
        .unwrap(),
    )
}
fn prepared(inputs: Arc<CheckedInputs>, reading: &str) -> PreparedObserved {
    let ask = format!("b=build({reading},on=@v/A)");
    let requests =
        resolve_native_for_test(inputs.law(), inputs.archmap(), &[&ask], &mut quiet()).unwrap();
    PreparedObserved {
        inputs,
        requests,
        object: None,
    }
}
fn start(p: &PreparedObserved) -> (Graph, NodeRef, Option<NodeRef>) {
    let env = Environment::with_prepared(p, &mut quiet()).unwrap();
    let mut g = Graph::new(&quiet());
    g.requests = p.requests().requests().to_vec();
    let a = crate::observed::architecture_result::build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[0],
        &mut quiet(),
    )
    .unwrap();
    let objects = if a.complete {
        crate::observed::object_component_diagram::retain(
            &mut g,
            p.shared_inputs(),
            a.reference,
            &mut quiet(),
        )
        .unwrap()
        .map(|o| o.base)
    } else {
        None
    };
    (g, a.reference, objects)
}
fn copy(g: &Graph, c: &Control) -> Graph {
    let mut p = Graph::new(c);
    p.nodes = g.nodes.clone();
    p.contexts = g.contexts.clone();
    p.frames = g.frames.clone();
    p.instances = g.instances.clone();
    p.iterations = g.iterations.clone();
    p.cases = g.cases.clone();
    p.universal_witnesses = g.universal_witnesses.clone();
    p.requests = g.requests.clone();
    p.checked_answers = g.checked_answers.clone();
    p.active = g.active;
    p
}
fn replay(p: &PreparedObserved, g: &Graph) {
    let env = Environment::with_prepared(p, &mut quiet()).unwrap();
    let mut prefix = copy(g, &quiet());
    prefix.nodes.clear();
    prefix.contexts.clear();
    for (i, n) in g.nodes.iter().enumerate() {
        prefix.active = g.contexts[i];
        env.validate(&prefix, n).unwrap();
        prefix.push(n.clone()).unwrap();
    }
}
fn data(g: &Graph, r: NodeRef) -> &Data {
    let Some(Payload::Construction(v)) = &g.get(r).unwrap().payload else {
        panic!()
    };
    let D::CircuitPattern(d) = &v.data else {
        panic!()
    };
    d
}
fn fact(id: &str, field: Option<&str>) -> Fact {
    let ty = match id {
        "A" | "B" => "Root",
        "p" | "q" => "Part",
        "x" => "External",
        _ => panic!(),
    };
    Fact {
        snapshot: "v".into(),
        subject: id.into(),
        field: field.map(|f| format!("Profile.{ty}.{f}").into()),
        atom: field.map(|f| format!("{id}-{f}")),
    }
}
fn expected() -> (Vec<Fact>, BTreeSet<Fact>, BTreeSet<(Fact, Fact)>) {
    let mut universe = vec![
        fact("p", Some("owner")),
        fact("p", Some("quantity")),
        fact("q", Some("owner")),
        fact("q", Some("quantity")),
        fact("x", Some("quantity")),
    ];
    universe.extend(["A", "B", "p", "q", "x"].map(|id| fact(id, None)));
    let family = [
        fact("A", None),
        fact("p", None),
        fact("p", Some("owner")),
        fact("p", Some("quantity")),
    ]
    .into_iter()
    .collect();
    let relations = [
        (fact("p", None), fact("p", Some("owner"))),
        (fact("p", None), fact("p", Some("quantity"))),
        (fact("p", Some("owner")), fact("A", None)),
    ]
    .into_iter()
    .collect();
    (universe, family, relations)
}
fn expected_queries(
    u: &[Fact],
    family: &BTreeSet<Fact>,
    relations: &BTreeSet<(Fact, Fact)>,
) -> Vec<Query> {
    let mut qs = vec![];
    for a in u {
        qs.push(Query::Atom {
            atom: a.clone(),
            present: family.contains(a),
        });
    }
    for a in u {
        for b in u {
            qs.push(Query::Relation {
                left: a.clone(),
                right: b.clone(),
                present: family.contains(a)
                    && family.contains(b)
                    && relations.contains(&(a.clone(), b.clone())),
            });
        }
    }
    for a in u {
        for b in u {
            qs.push(Query::Identification {
                left: a.clone(),
                right: b.clone(),
                present: a == b && family.contains(a),
            });
        }
    }
    qs
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
fn run(map: &str, reading: &str) -> (PreparedObserved, Graph, Diagram) {
    let p = prepared(inputs(map), reading);
    let (mut g, a, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let d = retain(&env, &mut g, p.shared_inputs(), a, o, &mut quiet())
        .unwrap()
        .unwrap();
    (p, g, d)
}
#[test]
fn all_queries_use_the_actual_common_universe_and_keep_equal_pattern_objects_distinct() {
    let (p, g, d) = run(MAP, "ProfileRead");
    assert_eq!(d.rows.len(), 2);
    assert_ne!(d.rows[0].object, d.rows[1].object);
    assert_ne!(d.rows[0].pattern, d.rows[1].pattern);
    let (u, f, r) = expected();
    let qs = expected_queries(&u, &f, &r);
    assert_eq!(qs.len(), 210);
    assert_eq!(
        data(&g, d.rows[0].pattern).output,
        data(&g, d.rows[1].pattern).output
    );
    for row in &d.rows {
        let data = data(&g, row.pattern);
        assert_eq!(data.output.universe, d.universe);
        assert_eq!(data.output.queries, qs);
        assert_eq!(data.source.profiles.profiles().len(), 2);
        assert_eq!(
            data.source.profiles.classes(),
            Some([vec![0, 1]].as_slice())
        );
        let node = g.get(row.pattern).unwrap();
        assert_eq!(node.ty, NodeType::Construction(T::CircuitPattern));
        assert_eq!(node.rule, Rule::Construction("circuit_pattern"));
        assert!(node.judgment.is_none() && node.reasons.is_empty() && node.evidence.is_empty());
        assert!(
            node.arguments.contains(&row.object)
                && node.arguments.contains(&d.universe)
                && node.arguments.contains(&d.architecture)
        );
        assert!(node.arguments.iter().all(|r| r.0 < row.pattern.0));
        let Json::Obj(ref fields) = data.wire() else {
            panic!()
        };
        assert_eq!(fields.len(), 2);
        assert_eq!(fields["universe"], d.universe.wire());
        assert_eq!(
            fields["queries"],
            Json::Arr(qs.iter().map(Query::wire).collect())
        );
        let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
        env.recheck_node(&g, node, row.pattern.0).unwrap();
    }
    let Some(Payload::Construction(v)) = &g.get(d.universe).unwrap().payload else {
        panic!()
    };
    assert!(matches!(&v.data,D::AtomUniverse(actual)if actual==&u));
    assert_eq!(
        qs.iter()
            .filter(|q| matches!(q, Query::Relation { present: true, .. }))
            .count(),
        3
    );
    assert_eq!(
        qs.iter()
            .filter(|q| matches!(q, Query::Identification { present: true, .. }))
            .count(),
        4
    );
    replay(&p, &g);
}
#[test]
fn missing_quantity_keeps_required_slots_and_uses_only_known_atoms_in_the_pattern() {
    let map = remove(MAP, "p-quantity");
    let (p, g, d) = run(&map, "ProfileRead");
    let (mut u, mut f, r) = expected();
    u.retain(|a| a != &fact("p", Some("quantity")));
    f.remove(&fact("p", Some("quantity")));
    let qs = expected_queries(&u, &f, &r);
    assert_eq!(qs.len(), 171);
    for row in &d.rows {
        let data = data(&g, row.pattern);
        assert_eq!(data.output.queries, qs);
        let slot = Fact {
            atom: None,
            ..fact("p", Some("quantity"))
        };
        assert!(
            data.source.profiles.profiles().iter().all(|p| p
                .configuration()
                .known()
                .requirements()
                .contains(&slot))
        );
        assert!(
            !data
                .source
                .profiles
                .construction()
                .universe()
                .contains(&fact("p", Some("quantity")))
        );
    }
    replay(&p, &g);
}
#[test]
fn unknown_ownership_retains_the_original_partial_graph_without_a_complete_pattern_table() {
    let p = prepared(inputs(&remove(MAP, "p-owner")), "ProfileRead");
    let (mut g, a, o) = start(&p);
    assert!(o.is_none());
    let old = copy(&g, &quiet());
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    assert!(
        retain(&env, &mut g, p.shared_inputs(), a, o, &mut quiet())
            .unwrap()
            .is_none()
    );
    assert_eq!(g.nodes, old.nodes);
    assert_eq!(g.contexts, old.contexts);
    assert_eq!(g.active, old.active);
    assert!(
        !g.nodes
            .iter()
            .any(|n| n.ty == NodeType::Construction(T::CircuitPattern))
    );
    assert!(g.nodes.iter().any(|n| n.reasons.iter().any(|r| {
        r.missing
            .iter()
            .any(|f| f.subject == "p" && f.field.as_deref() == Some("Profile.Part.owner"))
    })));
    replay(&p, &g);
}
#[test]
fn raw_quantity_values_do_not_create_new_geometry_or_merge_input_provenance() {
    let (p, g, d) = run(MAP, "ProfileRead");
    let (other, h, e) = run(
        &MAP.replace("\"value\":\"2\"", "\"value\":\"8\""),
        "ProfileRead",
    );
    for (x, y) in d.rows.iter().zip(&e.rows) {
        assert_eq!(
            data(&g, x.pattern).output.queries,
            data(&h, y.pattern).output.queries
        );
    }
    let foreign = Environment::with_prepared(&other, &mut quiet()).unwrap();
    assert!(
        foreign
            .recheck_node(&g, g.get(d.rows[0].pattern).unwrap(), d.rows[0].pattern.0)
            .is_err()
    );
    replay(&p, &g);
    replay(&other, &h);
}
#[test]
fn selected_reading_identity_and_same_named_subjects_in_another_snapshot_are_preserved() {
    let (p, g, d) = run(MAP, "ProfileRead");
    let (other, h, e) = run(MAP, "Alternative");
    assert_eq!(
        data(&g, d.rows[0].pattern).output.queries,
        data(&h, e.rows[0].pattern).output.queries
    );
    assert_ne!(
        g.get(d.rows[0].pattern).unwrap().scope.readings,
        h.get(e.rows[0].pattern).unwrap().scope.readings
    );
    let map=MAP.replace("\"snapshots\":[",r#""snapshots":[{"id":"w","origin":"model","subjects":[{"id":"A","type":"Profile.Root","origin":"model"},{"id":"p","type":"Profile.Part","origin":"model"}],"atoms":[{"id":"p-owner-w","subject":"p","field":"Profile.Part.owner","value":["w","A"],"origin":"model"}]},"#);
    assert_ne!(map, MAP);
    let (extended, j, t) = run(&map, "ProfileRead");
    let value = data(&j, t.rows[0].pattern);
    assert_eq!(value.source.profiles.construction().universe().len(), 13);
    assert_eq!(value.output.queries.len(), 351);
    for id in ["A", "p"] {
        for snapshot in ["v", "w"] {
            assert_eq!(
                value
                    .source
                    .profiles
                    .construction()
                    .universe()
                    .iter()
                    .filter(|a| a.subject == id && a.snapshot == snapshot && a.field.is_none())
                    .count(),
                1
            );
        }
    }
    for q in &value.output.queries {
        match q {
            Query::Atom { atom, present } if atom.snapshot == "w" => assert!(!present),
            Query::Relation {
                left,
                right,
                present,
            }
            | Query::Identification {
                left,
                right,
                present,
            } if left.snapshot == "w" || right.snapshot == "w" => assert!(!present),
            _ => {}
        }
    }
    replay(&p, &g);
    replay(&other, &h);
    replay(&extended, &j);
}
#[test]
fn altered_queries_source_tables_positions_edges_and_metadata_are_rejected() {
    let (p, g, d) = run(MAP, "ProfileRead");
    let r = d.rows[0].pattern;
    let n = g.get(r).unwrap();
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    env.recheck_node(&g, n, r.0).unwrap();
    for mode in 0..16 {
        let mut n = n.clone();
        let Some(Payload::Construction(v)) = &mut n.payload else {
            panic!()
        };
        let D::CircuitPattern(data) = &mut v.data else {
            panic!()
        };
        match mode {
            0 => {
                data.output.queries.pop();
            }
            1 => data.output.queries.push(data.output.queries[0].clone()),
            2 => data.output.queries.reverse(),
            3 => data.output.queries.swap(0, 1),
            4 => {
                let Query::Atom { present, .. } = &mut data.output.queries[0] else {
                    panic!()
                };
                *present = !*present;
            }
            5 => {
                let Query::Atom { atom, .. } = &mut data.output.queries[0] else {
                    panic!()
                };
                atom.atom = None;
            }
            6 => {
                let Query::Relation { left, .. } = &mut data.output.queries[10] else {
                    panic!()
                };
                *left = fact("A", None);
            }
            7 => data.output.universe = d.rows[0].object,
            8 => data.output.universe = r,
            9 => data.index = usize::MAX,
            10 => data.index = 1,
            11 => Arc::make_mut(&mut data.source).base += 1,
            12 => {
                let s = Arc::make_mut(&mut data.source);
                s.outputs[0].queries.reverse();
                data.output = s.outputs[0].clone();
            }
            13 => Arc::make_mut(&mut data.source).objects.objects.swap(0, 1),
            14 => Arc::make_mut(&mut data.source).diagram.rows.swap(0, 1),
            15 => Arc::make_mut(&mut data.source).universe = d.rows[0].object,
            _ => unreachable!(),
        };
        assert!(env.recheck_node(&g, &n, r.0).is_err(), "payload {mode}");
    }
    for mode in 0..9 {
        let mut n = n.clone();
        match mode {
            0 => n.ty = NodeType::Construction(T::AtomUniverse),
            1 => n.rule = Rule::Construction("object_algebra"),
            2 => n.arguments.clear(),
            3 => n.arguments.push(r),
            4 => n.scope = Scope::default(),
            5 => n.support.clear(),
            6 => n.evidence.push(r),
            7 => {
                n.reasons.push(Reason {
                    kind: ReasonKind::Missing,
                    request: "b".into(),
                    dependencies: vec![],
                    missing: vec![fact("p", Some("quantity"))],
                    location: None,
                });
            }
            8 => {
                let Some(Payload::Construction(v)) = &mut n.payload else {
                    panic!()
                };
                let Witness::Architecture(a) = &mut v.witness else {
                    panic!()
                };
                *a = Arc::new((**a).clone());
            }
            _ => unreachable!(),
        };
        assert!(env.recheck_node(&g, &n, r.0).is_err(), "node {mode}");
    }
    assert!(env.recheck_node(&g, n, r.0 + 1).is_err());
    let mut changed = copy(&g, &quiet());
    changed.requests[0].id = "other".into();
    assert!(env.recheck_node(&changed, n, r.0).is_err());
    let mut changed = copy(&g, &quiet());
    changed.contexts[r.0].instance = Some(usize::MAX);
    assert!(env.recheck_node(&changed, n, r.0).is_err());
    replay(&p, &g);
}
#[test]
fn absent_or_wrong_components_and_foreign_inputs_never_produce_a_fake_table() {
    let p = prepared(inputs(MAP), "ProfileRead");
    let (mut g, a, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let old = copy(&g, &quiet());
    assert!(
        retain(&env, &mut g, p.shared_inputs(), a, None, &mut quiet())
            .unwrap()
            .is_none()
    );
    assert_eq!(g.nodes, old.nodes);
    for bad in [a, NodeRef(usize::MAX)] {
        assert!(retain(&env, &mut g, p.shared_inputs(), a, Some(bad), &mut quiet()).is_err());
        assert_eq!(g.nodes, old.nodes);
    }
    let changed = inputs(&MAP.replace("\"value\":\"2\"", "\"value\":\"8\""));
    assert!(retain(&env, &mut g, changed, a, o, &mut quiet()).is_err());
    assert_eq!(g.nodes, old.nodes);
    g.active.request = 1;
    assert!(retain(&env, &mut g, p.shared_inputs(), a, o, &mut quiet()).is_err());
    assert_eq!(g.nodes, old.nodes);
}
#[test]
fn finished_patterns_recheck_after_a_later_request_without_allowing_foreign_creation() {
    let inputs = inputs(MAP);
    let requests = resolve_native_for_test(
        inputs.law(),
        inputs.archmap(),
        &[
            "b=build(ProfileRead,on=@v/A)",
            "later=build(ProfileRead,on=@v/B)",
        ],
        &mut quiet(),
    )
    .unwrap();
    let p = PreparedObserved {
        inputs,
        requests,
        object: None,
    };
    let (mut g, a, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let d = retain(&env, &mut g, p.shared_inputs(), a, o, &mut quiet())
        .unwrap()
        .unwrap();
    let original_contexts = g.contexts.clone();
    assert_eq!(d.rows.len(), 2);
    g.active.request = 1;
    let later = crate::observed::architecture_result::build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[1],
        &mut quiet(),
    )
    .unwrap();
    assert!(later.complete);
    assert_eq!(g.context_at(later.reference.0).request, 1);
    let active = g.active;
    for row in &d.rows {
        assert_eq!(g.context_at(row.pattern.0).request, 0);
        let fresh = Environment::with_prepared(&p, &mut quiet()).unwrap();
        let checked = fresh.recheck_node(&g, g.get(row.pattern).unwrap(), row.pattern.0);
        assert!(checked.is_ok(), "{checked:?}");
        assert_eq!(g.active, active);
    }
    assert_eq!(&g.contexts[..original_contexts.len()], &original_contexts);
    let before = copy(&g, &quiet());
    let fresh = Environment::with_prepared(&p, &mut quiet()).unwrap();
    assert!(retain(&fresh, &mut g, p.shared_inputs(), a, o, &mut quiet()).is_err());
    assert_eq!(g.nodes, before.nodes);
    assert_eq!(g.contexts, before.contexts);
    assert_eq!(g.active, active);
    for mode in 0..3 {
        let mut changed = copy(&g, &quiet());
        match mode {
            0 => changed.requests[0].id = "forged".into(),
            1 => changed.contexts[a.0].request = 1,
            2 => changed.contexts[d.rows[0].pattern.0].request = 1,
            _ => unreachable!(),
        }
        let fresh = Environment::with_prepared(&p, &mut quiet()).unwrap();
        let r = d.rows[0].pattern;
        assert!(
            fresh
                .recheck_node(&changed, changed.get(r).unwrap(), r.0)
                .is_err()
        );
    }
}
#[test]
fn four_stops_keep_complete_pattern_nodes_and_the_exact_original_context_prefix() {
    use std::{cell::Cell, rc::Rc};
    let p = prepared(inputs(MAP), "ProfileRead");
    let (initial, a, o) = start(&p);
    let seen = Rc::new(Cell::new(0));
    let count = seen.clone();
    let mut c = Control::new(move |point| {
        if matches!(
            point,
            Checkpoint::ConfigurationProfile | Checkpoint::NativeResultNode
        ) {
            count.set(count.get() + 1)
        }
        None
    });
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut full = copy(&initial, &c);
    let all = retain(&env, &mut full, p.shared_inputs(), a, o, &mut c)
        .unwrap()
        .unwrap();
    assert_eq!(all.rows.len(), 2);
    let total = seen.get();
    assert!(total > 420);
    let mut partial = false;
    let mut finished = false;
    for signal in [crate::result::Signal::Int, crate::result::Signal::Term] {
        for at in [1, total / 2, total - 3, total - 2, total - 1, total] {
            let seen = Rc::new(Cell::new(0));
            let count = seen.clone();
            let mut c = Control::new(move |point| {
                if matches!(
                    point,
                    Checkpoint::ConfigurationProfile | Checkpoint::NativeResultNode
                ) {
                    count.set(count.get() + 1)
                }
                (count.get() >= at).then_some(signal)
            });
            let mut g = copy(&initial, &c);
            let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
            assert!(matches!(
                retain(&env, &mut g, p.shared_inputs(), a, o, &mut c),
                Err(ValidationFailure::Stop(_))
            ));
            assert_eq!(g.active, initial.active);
            assert!(env.state.architecture_ref().is_none());
            assert!(g.nodes.len() <= full.nodes.len());
            for (i, n) in g.nodes.iter().enumerate() {
                assert_eq!(
                    n.wire(i, &g.nodes[..i]),
                    full.nodes[i].wire(i, &full.nodes[..i])
                );
            }
            assert_eq!(g.contexts, &full.contexts[..g.nodes.len()]);
            partial |= g.nodes.len() > initial.nodes.len() && g.nodes.len() < full.nodes.len();
            finished |= g.nodes.len() == full.nodes.len();
            replay(&p, &g);
        }
    }
    assert!(partial && finished);
}

#[test]
fn shared_external_references_preserve_identity_and_do_not_import_external_fields() {
    let definition = include_bytes!("../../../tests/fixtures/internal-arrow.atoms.json");
    let law = include_str!("../../../tests/fixtures/internal-arrow.law");
    let map = include_str!("../../../tests/fixtures/internal-arrow.archmap.json");
    let bundle = |map: &str| {
        let defs = crate::definition::check_definitions(&[("definition0", definition)]).unwrap();
        let digest = &defs.vocabularies()["Flow"].digest;
        Arc::new(
            crate::input::check_inputs(
                crate::input::InputSources::from_bytes(
                    vec![definition.to_vec()],
                    law.replace("@FLOW_DIGEST@", digest).into_bytes(),
                    map.replace("@FLOW_DIGEST@", digest).into_bytes(),
                ),
                &mut quiet(),
            )
            .unwrap(),
        )
    };
    let p = prepared(bundle(map), "FlowRead");
    let (mut g, a, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let d = retain(&env, &mut g, p.shared_inputs(), a, o, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(d.rows.len(), 3);
    let scalar = |subject: &str, field: Option<&str>| {
        let ty = if ["A", "B"].contains(&subject) {
            "Root"
        } else if ["e", "f", "g"].contains(&subject) {
            "Step"
        } else if ["x", "y"].contains(&subject) {
            "External"
        } else {
            "Node"
        };
        Fact {
            snapshot: "v".into(),
            subject: subject.into(),
            field: field.map(|f| format!("Flow.{ty}.{f}").into()),
            atom: field.map(|f| format!("{subject}-{f}")),
        }
    };
    for (index, row) in d.rows.iter().enumerate() {
        let data = data(&g, row.pattern);
        let n = data.source.profiles.construction().universe().len();
        assert_eq!(data.output.queries.len(), n + 2 * n * n);
        let membership = |f: &Fact| {
            data.output
                .queries
                .iter()
                .find_map(|q| match q {
                    Query::Atom { atom, present } if atom == f => Some(*present),
                    _ => None,
                })
                .unwrap()
        };
        let relation = |a: &Fact, b: &Fact| {
            data.output
                .queries
                .iter()
                .find_map(|q| match q {
                    Query::Relation {
                        left,
                        right,
                        present,
                    } if left == a && right == b => Some(*present),
                    _ => None,
                })
                .unwrap()
        };
        let equal = |a: &Fact, b: &Fact| {
            data.output
                .queries
                .iter()
                .find_map(|q| match q {
                    Query::Identification {
                        left,
                        right,
                        present,
                    } if left == a && right == b => Some(*present),
                    _ => None,
                })
                .unwrap()
        };
        for id in ["r", "x", "y"] {
            assert!(membership(&scalar(id, None)));
            assert!(
                !data.source.profiles.profiles()[index]
                    .domain()
                    .known()
                    .iter()
                    .any(|f| f.subject == id)
            );
        }
        for field in [
            scalar("r", Some("owner")),
            scalar("r", Some("quantity")),
            scalar("x", Some("quantity")),
            scalar("y", Some("quantity")),
        ] {
            assert!(!membership(&field));
        }
        assert!(!relation(&scalar("r", Some("owner")), &scalar("B", None)));
        assert!(!equal(
            &scalar("p", Some("owner")),
            &scalar("q", Some("owner"))
        ));
        for (subject, at) in [("p", 1), ("q", 2)] {
            assert_eq!(
                relation(&scalar(subject, Some("pair")), &scalar("x", None)),
                index == 0 || index == at
            );
            assert_eq!(
                relation(&scalar(subject, Some("owner")), &scalar("A", None)),
                index == 0 || index == at
            );
        }
    }
    replay(&p, &g);
    let missing = prepared(bundle(&remove(map, "p-links")), "FlowRead");
    let (mut graph, a, o) = start(&missing);
    assert!(o.is_none());
    let before = copy(&graph, &quiet());
    let env = Environment::with_prepared(&missing, &mut quiet()).unwrap();
    assert!(
        retain(
            &env,
            &mut graph,
            missing.shared_inputs(),
            a,
            o,
            &mut quiet()
        )
        .unwrap()
        .is_none()
    );
    assert_eq!(graph.nodes, before.nodes);
    assert_eq!(graph.contexts, before.contexts);
    replay(&missing, &graph);
}
