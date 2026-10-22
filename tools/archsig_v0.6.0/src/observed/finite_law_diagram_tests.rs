use super::*;
use crate::observed::{
    control::{Limits, Usage},
    evaluate_observed_bytes,
    input::InputSources,
};

fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
const DEFINITION: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Finite","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Finite.Root","meaning":"有限入力の対象。","parameters":[],"fields":[],"alignments":[]},{"kind":"entity","name":"Finite.Part","meaning":"有限入力の対象。","parameters":[{"name":"owner","type":["Ref","Finite.Root"],"meaning":"元の型付き値。"}],"fields":[{"name":"quantity","type":["Fp","2"],"meaning":"元の型付き値。"}],"alignments":[]},{"kind":"correspondence","name":"Finite.Migration","meaning":"有限入力の対象。","parameters":[{"name":"from","type":["Ref","Finite.Root"],"meaning":"元の型付き値。"},{"name":"to","type":["Ref","Finite.Root"],"meaning":"元の型付き値。"}],"fields":[{"name":"states","type":["Map",["Owned","Finite.Part","from"],["Owned","Finite.Part","to"]],"meaning":"元の型付き値。"}],"alignments":[]}]}]}"#;
const MAP: &str = r#"{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{"namespace":"Finite","version":"1","digest":"@DIGEST@"}],"sources":[],"origins":[{"id":"model","mode":"specification","method":"独立の有限入力。","locations":[],"note":"原始値と対応だけを記録する。"}],"snapshots":[{"id":"v","origin":"model","subjects":[{"id":"a","type":"Finite.Root","origin":"model"},{"id":"b","type":"Finite.Root","origin":"model"},{"id":"p","type":"Finite.Part","origin":"model"},{"id":"q","type":"Finite.Part","origin":"model"},{"id":"m","type":"Finite.Migration","origin":"model"}],"atoms":[{"id":"po","subject":"p","field":"Finite.Part.owner","value":["v","a"],"origin":"model"},{"id":"qo","subject":"q","field":"Finite.Part.owner","value":["v","b"],"origin":"model"},{"id":"px","subject":"p","field":"Finite.Part.quantity","value":"0","origin":"model"},{"id":"mx","subject":"m","field":"Finite.Migration.from","value":["v","a"],"origin":"model"},{"id":"my","subject":"m","field":"Finite.Migration.to","value":["v","b"],"origin":"model"},{"id":"mm","subject":"m","field":"Finite.Migration.states","value":[[["v","p"],["v","q"]]],"origin":"model"},{"id":"qx","subject":"q","field":"Finite.Part.quantity","value":"1","origin":"model"}]}]}"#;
fn custom_sources(definition: &str, map: &str, body: &str) -> InputSources {
    let defs =
        crate::definition::check_definitions(&[("definition0", definition.as_bytes())]).unwrap();
    let digest = &defs.vocabularies["Finite"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Chosen{{use vocabulary Finite version \"1\" digest \"{digest}\";{body}}}"
    );
    InputSources::from_bytes(
        vec![definition.as_bytes().to_vec()],
        law.into_bytes(),
        map.replace("@DIGEST@", digest).into_bytes(),
    )
}
fn sources(missing: bool, body: &str) -> InputSources {
    let map = if missing {
        MAP.replace(r#",{"id":"qx","subject":"q","field":"Finite.Part.quantity","value":"1","origin":"model"}"#,"")
    } else {
        MAP.into()
    };
    custom_sources(DEFINITION, &map, body)
}
const BODY: &str = "law required zero(c:Part):c.quantity=0;law optional one(c:Part):c.quantity=1;";
fn example(missing: bool, body: &str) -> ObservedEvaluation {
    evaluate_observed_bytes(
        sources(missing, body),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &mut quiet(),
    )
    .unwrap()
}
fn replay(
    e: &ObservedEvaluation,
    nodes: &[Node],
    contexts: &[crate::observed::call::Context],
) -> Result<Graph, ValidationFailure> {
    let mut c = quiet();
    let env = Environment::with_requests(
        e.prepared.inputs(),
        e.prepared.requests().requests(),
        &mut c,
    )?;
    let mut g = Graph::new(&c);
    g.requests = e.prepared.requests().requests().to_vec();
    g.frames = e.frames.clone();
    g.iterations = e.iterations.clone();
    g.instances = e.instances.clone();
    g.cases = e.cases.clone();
    g.universal_witnesses = e.universal_witnesses.clone();
    g.checked_answers = e.answers.iter().cloned().enumerate().collect();
    for (index, n) in nodes.iter().enumerate() {
        g.active = contexts[index];
        env.validate(&g, n)?;
        g.push(n.clone())?;
    }
    Ok(g)
}
fn graph(e: &ObservedEvaluation) -> Graph {
    replay(e, &e.nodes, &e.contexts).unwrap()
}
fn architecture(g: &Graph, root: &str) -> NodeRef {
    NodeRef(g.nodes.iter().position(|n|matches!(&n.payload,Some(Payload::Construction(v)) if matches!((&v.witness,&v.data),(Witness::Architecture(a),D::Architecture{..}) if a.construction().root().subject==root))).unwrap())
}
fn data(g: &Graph, r: NodeRef) -> &Data {
    let Some(Payload::Construction(v)) = &g.nodes[r.0].payload else {
        panic!("native")
    };
    let D::FiniteLaw(data) = &v.data else {
        panic!("finite")
    };
    data
}
fn wire(g: &Graph, r: NodeRef) -> Json {
    data(g, r).wire()
}
fn property(g: &Graph, r: NodeRef, name: &str) -> Json {
    let j = wire(g, r);
    let Json::Obj(o) = &j else { panic!("record") };
    o[name].clone()
}
fn coordinates(g: &Graph, r: NodeRef) -> Vec<String> {
    let Part::Function { values, .. } = data(g, r).part() else {
        panic!("function")
    };
    values
        .iter()
        .map(|r| match g.scalar(*r).unwrap() {
            Scalar::Z(n) => n.to_string(),
            _ => panic!("Z"),
        })
        .collect()
}
#[test]
fn finite_native_diagram_keeps_wire_values_original_nu_epsilon_and_ideal_generators() {
    let e = example(false, BODY);
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let start = g.nodes.len();
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(property(&g, d.domain, "kind"), Json::str("finite"));
    assert_eq!(
        property(&g, d.domain, "type"),
        Json::Arr(vec![Json::str("Fp"), Json::str("2")])
    );
    let Part::Domain { elements, .. } = data(&g, d.domain).part() else {
        panic!("D")
    };
    assert_eq!(elements.len(), 2);
    assert!(matches!(g.scalar(elements[0]).unwrap(),Scalar::Fp{value,..} if value==&0.into()));
    assert!(matches!(g.scalar(elements[1]).unwrap(),Scalar::Fp{value,..} if value==&1.into()));
    assert_eq!(
        wire(&g, d.ring),
        Json::obj([
            ("kind", Json::str("finite_functions")),
            ("domain", d.domain.wire())
        ])
    );
    assert_eq!(
        wire(&g, d.target),
        Json::obj([("kind", Json::str("scalar")), ("scalar", Json::str("Z"))])
    );
    assert_eq!(d.nu.len(), 2);
    let origin = &data(&g, d.ring).source.architecture;
    assert_eq!(
        d.components
            .iter()
            .map(|(i, p)| {
                assert_eq!(p.as_deref(), Some([].as_slice()));
                origin.readings().instances()[*i].declaration().name.clone()
            })
            .collect::<Vec<_>>(),
        ["Chosen.one", "Chosen.zero"]
    );
    assert_eq!(coordinates(&g, d.nu[0]), ["1", "0"]);
    assert_eq!(coordinates(&g, d.nu[1]), ["0", "1"]);
    assert_eq!(coordinates(&g, d.epsilon[0].unwrap()), ["1", "1"]);
    assert_eq!(coordinates(&g, d.epsilon[1].unwrap()), ["0", "0"]);
    for (i, w) in d.witnesses.iter().enumerate() {
        assert_eq!(property(&g, *w, "kind"), Json::str("witness"));
        assert_eq!(
            data(&g, *w).part(),
            &Part::Ideal {
                ring: d.ring,
                generators: vec![d.nu[i]],
                required: false
            }
        );
    }
    assert_eq!(
        data(&g, d.required).part(),
        &Part::Ideal {
            ring: d.ring,
            generators: vec![d.nu[1]],
            required: true
        }
    );
    let ev = d.evaluation.unwrap();
    let Part::Evaluation {
        source,
        target,
        basis_images,
    } = data(&g, ev).part()
    else {
        panic!("map")
    };
    assert_eq!((*source, *target), (d.ring, d.target));
    assert_eq!(
        basis_images
            .iter()
            .map(|r| match g.scalar(*r).unwrap() {
                Scalar::Z(n) => n.to_string(),
                _ => panic!("Z"),
            })
            .collect::<Vec<_>>(),
        ["1", "0"]
    );
    assert_eq!(property(&g, ev, "kind"), Json::str("finite_functions"));
    for (i, n) in g.nodes.iter().enumerate().skip(start) {
        assert!(n.arguments.iter().all(|r| r.0 < i));
        assert!(n.scope.assignments);
        assert!(!n.scope.completions);
        assert!(n.scope.readings.contains("Chosen"));
        assert!(n.support.iter().any(|f| f.atom.as_deref() == Some("px")));
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn finite_diagram_keeps_target_root_and_owned_object_identity_separate() {
    let e = example(false, BODY);
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let b = architecture(&g, "b");
    let source = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
        .unwrap()
        .unwrap();
    let target = retain(&mut g, e.prepared.shared_inputs(), b, 0, &mut quiet())
        .unwrap()
        .unwrap();
    let owned = retain(&mut g, e.prepared.shared_inputs(), a, 1, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(coordinates(&g, source.nu[1]), ["0", "1"]);
    assert_eq!(coordinates(&g, target.nu[1]), ["0", "1"]);
    assert_eq!(coordinates(&g, source.epsilon[1].unwrap()), ["0", "0"]);
    assert_eq!(coordinates(&g, target.epsilon[1].unwrap()), ["1", "1"]);
    assert!(!Arc::ptr_eq(
        &data(&g, source.ring).source,
        &data(&g, target.ring).source
    ));
    assert_eq!(data(&g, owned.ring).source.object, 1);
    assert_eq!(data(&g, source.ring).source.object, 0);
    assert_eq!(data(&g, source.ring).source.reference, a);
    assert_eq!(data(&g, target.ring).source.reference, b);
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn missing_observation_omits_evaluation_and_epsilon_without_pruning_symbolic_domain() {
    let e = example(true, BODY);
    let mut g = graph(&e);
    let b = architecture(&g, "b");
    let d = retain(&mut g, e.prepared.shared_inputs(), b, 0, &mut quiet())
        .unwrap()
        .unwrap();
    assert!(matches!(
        Environment::new(e.prepared.inputs(), &mut quiet())
            .unwrap()
            .field("v", "q", "Finite.Part.quantity")
            .unwrap()
            .slot,
        Slot::Missing
    ));
    assert!(d.evaluation.is_none());
    assert_eq!(d.epsilon, [None, None]);
    assert_eq!(coordinates(&g, d.nu[0]), ["1", "0"]);
    assert_eq!(coordinates(&g, d.nu[1]), ["0", "1"]);
    let Part::Domain { elements, .. } = data(&g, d.domain).part() else {
        panic!("D")
    };
    assert_eq!(elements.len(), 2);
    assert!(
        !g.nodes[d.ring.0]
            .support
            .iter()
            .any(|f| f.atom.as_deref() == Some("qx"))
    );
    assert_eq!(property(&g, d.required, "kind"), Json::str("obstruction"));
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn empty_law_keeps_unit_assignment_domain_and_empty_required_generators() {
    let e = example(false, "");
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
        .unwrap()
        .unwrap();
    assert!(d.nu.is_empty() && d.epsilon.is_empty() && d.witnesses.is_empty());
    let Part::Domain { ty, elements } = data(&g, d.domain).part() else {
        panic!("D")
    };
    assert_eq!(ty, &Type::Unit);
    assert_eq!(elements.len(), 1);
    assert!(matches!(g.scalar(elements[0]).unwrap(), Scalar::Unit));
    assert_eq!(
        data(&g, d.required).part(),
        &Part::Ideal {
            ring: d.ring,
            generators: vec![],
            required: true
        }
    );
    assert!(d.evaluation.is_some());
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn diagram_recheck_rejects_plan_values_generators_scope_provenance_and_consumer_changes() {
    let e = example(false, BODY);
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let b = architecture(&g, "b");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
        .unwrap()
        .unwrap();
    let source = data(&g, d.ring).source.clone();
    let a = source.architecture.clone();
    source
        .recheck(e.prepared.inputs(), &a, 0, &mut quiet())
        .unwrap();
    assert!(
        source
            .recheck(e.prepared.inputs(), &a, 1, &mut quiet())
            .is_err()
    );
    let Some(Payload::Construction(v)) = &g.get(b).unwrap().payload else {
        panic!("native")
    };
    let Witness::Architecture(other) = &v.witness else {
        panic!("architecture")
    };
    assert!(
        source
            .recheck(e.prepared.inputs(), other, 0, &mut quiet())
            .is_err()
    );
    let other = example(true, BODY);
    assert!(
        source
            .recheck(other.prepared.inputs(), &a, 0, &mut quiet())
            .is_err()
    );
    let mut changed = (*source).clone();
    changed.parts.swap(0, 1);
    assert!(
        changed
            .recheck(e.prepared.inputs(), &a, 0, &mut quiet())
            .is_err()
    );
    let mut changed = (*source).clone();
    changed.support.clear();
    assert!(
        changed
            .recheck(e.prepared.inputs(), &a, 0, &mut quiet())
            .is_err()
    );
    let mut changed = (*source).clone();
    changed.scope.assignments = false;
    assert!(
        changed
            .recheck(e.prepared.inputs(), &a, 0, &mut quiet())
            .is_err()
    );
    let mut changed = (*source).clone();
    changed.outputs.nu.reverse();
    assert!(
        changed
            .recheck(e.prepared.inputs(), &a, 0, &mut quiet())
            .is_err()
    );
    let mut changed = (*source).clone();
    changed.outputs.points.reverse();
    assert!(
        changed
            .recheck(e.prepared.inputs(), &a, 0, &mut quiet())
            .is_err()
    );
    let mut changed = (*source).clone();
    let index = d.required.0 - source.base;
    if let Part::Ideal { generators, .. } = &mut changed.parts[index] {
        generators.push(d.nu[0]);
    }
    assert!(
        changed
            .recheck(e.prepared.inputs(), &a, 0, &mut quiet())
            .is_err()
    );
    for change in 0..5 {
        let mut nodes = g.nodes.clone();
        let n = &mut nodes[d.ring.0];
        match change {
            0 => n.arguments.clear(),
            1 => n.scope.assignments = false,
            2 => n.support.clear(),
            3 => n.ty = NodeType::Construction(T::Ideal),
            _ => {
                let Some(Payload::Construction(v)) = &mut n.payload else {
                    panic!("native")
                };
                let D::FiniteLaw(data) = &mut v.data else {
                    panic!("finite")
                };
                data.index = usize::MAX;
            }
        }
        assert!(replay(&e, &nodes, &g.contexts).is_err(), "change {change}");
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn tuple_domain_preserves_fp_bool_leaf_values_and_evaluation_basis_order() {
    let definition = DEFINITION.replace(r#"["Fp","2"]"#, r#"["Tuple",["Fp","2"],"Bool"]"#);
    let map = MAP
        .replace(r#""value":"0""#, r#""value":["0",true]"#)
        .replace(r#""value":"1""#, r#""value":["1",false]"#);
    let e = evaluate_observed_bytes(
        custom_sources(
            &definition,
            &map,
            "law required zero(c:Part):c.quantity=(0,false);",
        ),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &mut quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
        .unwrap()
        .unwrap();
    let Part::Domain { ty, elements } = data(&g, d.domain).part() else {
        panic!("D")
    };
    assert_eq!(ty, &Type::Tuple(vec![Type::Fp("2".into()), Type::Bool]));
    assert_eq!(elements.len(), 4);
    for (i, r) in elements.iter().enumerate() {
        assert_eq!(
            g.scalar(*r).unwrap(),
            &Scalar::Tuple(vec![
                Scalar::Fp {
                    modulus: "2".into(),
                    value: (i / 2).into()
                },
                Scalar::Bool(i % 2 == 1)
            ])
        );
    }
    assert_eq!(
        d.components
            .iter()
            .map(|(_, p)| p.clone())
            .collect::<Vec<_>>(),
        [Some(vec![0]), Some(vec![1])]
    );
    assert_eq!(coordinates(&g, d.nu[0]), ["0", "0", "1", "1"]);
    assert_eq!(coordinates(&g, d.nu[1]), ["0", "1", "0", "1"]);
    assert_eq!(coordinates(&g, d.epsilon[0].unwrap()), ["0", "0", "0", "0"]);
    assert_eq!(coordinates(&g, d.epsilon[1].unwrap()), ["1", "1", "1", "1"]);
    let Part::Evaluation { basis_images, .. } = data(&g, d.evaluation.unwrap()).part() else {
        panic!("evaluation")
    };
    assert_eq!(
        basis_images
            .iter()
            .map(|r| match g.scalar(*r).unwrap() {
                Scalar::Z(n) => n.to_string(),
                _ => panic!("Z"),
            })
            .collect::<Vec<_>>(),
        ["0", "1", "0", "0"]
    );
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn outside_finite_range_and_wrong_producer_never_append_a_completed_diagram() {
    let definition = DEFINITION.replace(r#"["Fp","2"]"#, r#""Z""#);
    let e = evaluate_observed_bytes(
        custom_sources(&definition, MAP, BODY),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &mut quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let before = g.nodes.len();
    assert!(
        retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
            .unwrap()
            .is_none()
    );
    assert_eq!(g.nodes.len(), before);
    let e = example(false, BODY);
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let before = g.nodes.len();
    g.active.request = usize::MAX;
    assert!(retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet()).is_err());
    assert_eq!(g.nodes.len(), before);
    g.active.request = 0;
    assert!(
        retain(
            &mut g,
            e.prepared.shared_inputs(),
            a,
            usize::MAX,
            &mut quiet()
        )
        .is_err()
    );
    assert_eq!(g.nodes.len(), before);
}
fn stopping(mode: usize, at: usize) -> Control {
    let seen = std::rc::Rc::new(std::cell::Cell::new(0));
    Control::new(
        Limits {
            time_ms: (mode == 2).then_some(1),
            memory_mib: (mode == 3).then_some(1),
        },
        move |p| {
            if p == Checkpoint::FiniteLawFunction {
                seen.set(seen.get() + 1);
            }
            let stop = seen.get() >= at;
            Usage {
                signal: if stop && mode < 2 {
                    Some(if mode == 0 {
                        crate::result::Signal::Int
                    } else {
                        crate::result::Signal::Term
                    })
                } else {
                    None
                },
                elapsed_ms: u128::from(stop && mode == 2),
                memory_mib: u128::from(stop && mode == 3),
            }
        },
    )
}
#[test]
fn all_four_stops_keep_unfinished_plan_private_and_preserve_completed_prefix_nodes() {
    let e = example(false, BODY);
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let before = g.nodes.len();
    let count = std::rc::Rc::new(std::cell::Cell::new(0));
    let seen = count.clone();
    let mut c = Control::new(Limits::default(), move |p| {
        if p == Checkpoint::FiniteLawFunction {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut c)
        .unwrap()
        .unwrap();
    let source = data(&g, d.ring).source.clone();
    let total = count.get();
    assert!(total > 20);
    for mode in 0..4 {
        for at in [1, 5, total - 1, total] {
            let mut g = graph(&e);
            let a = architecture(&g, "a");
            assert!(matches!(
                retain(
                    &mut g,
                    e.prepared.shared_inputs(),
                    a,
                    0,
                    &mut stopping(mode, at)
                ),
                Err(ValidationFailure::Stop(_))
            ));
            if at <= 5 {
                assert_eq!(g.nodes.len(), before);
            }
            // A stopped caller receives no Diagram; any retained prefix consists of independently complete nodes.
            replay(&e, &g.nodes, &g.contexts).unwrap();
        }
        assert!(matches!(
            source.recheck(
                e.prepared.inputs(),
                &source.architecture,
                0,
                &mut stopping(mode, 1)
            ),
            Err(ValidationFailure::Stop(_))
        ));
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn reading_identity_and_cached_validation_cannot_be_exchanged_between_authentic_diagrams() {
    let input = sources(false, BODY);
    let law = std::str::from_utf8(input.law().bytes()).unwrap();
    let rest = law.split_once("reading Chosen").unwrap().1;
    let input = InputSources::from_bytes(
        input
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        format!("{law}reading Other{rest}").into_bytes(),
        input.archmap().bytes().to_vec(),
    );
    let e = evaluate_observed_bytes(
        input,
        &[
            "x=map(Finite.Migration,on=@v/m,reading=Chosen)",
            "y=map(Finite.Migration,on=@v/m,reading=Other)",
        ],
        &mut quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let choose = |g: &Graph, name: &str| {
        NodeRef(g.nodes.iter().position(|n|matches!(&n.payload,Some(Payload::Construction(v)) if matches!((&v.witness,&v.data),(Witness::Architecture(a),D::Architecture{..}) if a.construction().root().subject=="a"&&a.construction().reading()==name))).unwrap())
    };
    let a = choose(&g, "Chosen");
    let b = choose(&g, "Other");
    g.active = g.context_at(a.0);
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
        .unwrap()
        .unwrap();
    g.active = g.context_at(b.0);
    let other = retain(&mut g, e.prepared.shared_inputs(), b, 0, &mut quiet())
        .unwrap()
        .unwrap();
    assert!(g.nodes[d.ring.0].scope.readings.contains("Chosen"));
    assert!(!g.nodes[d.ring.0].scope.readings.contains("Other"));
    assert!(g.nodes[other.ring.0].scope.readings.contains("Other"));
    assert!(!g.nodes[other.ring.0].scope.readings.contains("Chosen"));
    let source = &data(&g, d.ring).source;
    let second = &data(&g, other.ring).source;
    assert!(
        source
            .recheck(e.prepared.inputs(), &second.architecture, 0, &mut quiet())
            .is_err()
    );
    let mut c = quiet();
    let env = Environment::with_requests(
        e.prepared.inputs(),
        e.prepared.requests().requests(),
        &mut c,
    )
    .unwrap();
    let Some(Payload::Construction(first)) = &g.get(d.ring).unwrap().payload else {
        panic!("first")
    };
    let Some(Payload::Construction(second_value)) = &g.get(other.ring).unwrap().payload else {
        panic!("second")
    };
    env.recheck_finite_law_diagram(&g, first).unwrap();
    env.recheck_finite_law_diagram(&g, second_value).unwrap();
    let mut forged = (**first).clone();
    let D::FiniteLaw(data) = &mut forged.data else {
        panic!("finite")
    };
    data.source = second.clone();
    assert!(env.recheck_finite_law_diagram(&g, &forged).is_err());
    env.recheck_finite_law_diagram(&g, first).unwrap();
    let stop = std::rc::Rc::new(std::cell::Cell::new(false));
    let flag = stop.clone();
    let mut c = Control::new(Limits::default(), move |_| Usage {
        signal: flag.get().then_some(crate::result::Signal::Int),
        ..Usage::default()
    });
    let env = Environment::with_requests(
        e.prepared.inputs(),
        e.prepared.requests().requests(),
        &mut c,
    )
    .unwrap();
    env.recheck_finite_law_diagram(&g, first).unwrap();
    stop.set(true);
    assert!(matches!(
        env.recheck_finite_law_diagram(&g, first),
        Err(ValidationFailure::Stop(_))
    ));
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn owned_reference_domain_keeps_original_membership_conditions_with_primitive_value_types() {
    let definition=DEFINITION.replace(r#""fields":[{"name":"quantity""#,r#""fields":[{"name":"link","type":["Owned","Finite.Part","owner"],"meaning":"同じ根に属する参照。"},{"name":"quantity""#);
    let map=MAP.replace(r#"{"id":"qx""#,r#"{"id":"pl","subject":"p","field":"Finite.Part.link","value":["v","p"],"origin":"model"},{"id":"ql","subject":"q","field":"Finite.Part.link","value":["v","q"],"origin":"model"},{"id":"qx""#);
    let map=map.replace(r#"{"id":"m","type":"Finite.Migration""#,r#"{"id":"r","type":"Finite.Part","origin":"model"},{"id":"m","type":"Finite.Migration""#)
        .replace(r#"{"id":"qx""#,r#"{"id":"ro","subject":"r","field":"Finite.Part.owner","value":["v","a"],"origin":"model"},{"id":"rl","subject":"r","field":"Finite.Part.link","value":["v","r"],"origin":"model"},{"id":"qx""#)
        .replace(r#""value":[[["v","p"],["v","q"]]]"#,r#""value":[[["v","p"],["v","q"]],[["v","r"],["v","q"]]]"#);
    let e = evaluate_observed_bytes(
        custom_sources(
            &definition,
            &map,
            "law required reflexive(c:Part):c.link=c.link;",
        ),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &mut quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let Some(Payload::Construction(v)) = &g.get(a).unwrap().payload else {
        panic!("Architecture")
    };
    let Witness::Architecture(origin) = &v.witness else {
        panic!("origin")
    };
    let full =
        finite_automatic_law_family(e.prepared.inputs(), origin.readings(), &mut quiet()).unwrap();
    let f = full.family().unwrap();
    assert!(f.is_complete());
    assert!(f.types().iter().any(|t| matches!(t, Type::Owned(..))));
    let original_types = f.types().to_vec();
    let positions = f.positions().to_vec();
    let expected = f.domain().to_vec();
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
        .unwrap()
        .unwrap();
    let Part::Domain { ty, elements } = data(&g, d.domain).part() else {
        panic!("D")
    };
    let erased = original_types.iter().map(Type::erase).collect::<Vec<_>>();
    let expected_type = match erased.as_slice() {
        [] => Type::Unit,
        [t] => t.clone(),
        v => Type::Tuple(v.to_vec()),
    };
    assert_eq!(ty, &expected_type);
    assert_eq!(elements.len(), expected.len());
    assert!(elements.len() > 1);
    let env = Environment::new(e.prepared.inputs(), &mut quiet()).unwrap();
    for (reference, index) in elements.iter().zip(&d.points) {
        let point = &expected[*index];
        let raw = match point.as_slice() {
            [] => Scalar::Unit,
            [v] => v.clone(),
            v => Scalar::Tuple(v.to_vec()),
        };
        assert_eq!(g.scalar(*reference).unwrap(), &raw);
        let get_owner = |subject: &str| -> (String, String) {
            if let Some(i) = positions.iter().position(|p| {
                p.subject == subject && p.field.as_deref() == Some("Finite.Part.owner")
            }) {
                let Scalar::Subject {
                    snapshot, subject, ..
                } = &point[i]
                else {
                    panic!("candidate owner")
                };
                (snapshot.clone(), subject.clone())
            } else {
                let Slot::Known {
                    value: crate::archmap::Value::Ref { snapshot, subject },
                    ..
                } = &env.field("v", subject, "Finite.Part.owner").unwrap().slot
                else {
                    panic!("original owner")
                };
                (snapshot.clone(), subject.clone())
            }
        };
        for (i, p) in positions
            .iter()
            .enumerate()
            .filter(|(_, p)| p.field.as_deref() == Some("Finite.Part.link"))
        {
            let Scalar::Subject {
                subject: target, ..
            } = &point[i]
            else {
                panic!("link")
            };
            assert_eq!(get_owner(&p.subject), get_owner(target));
        }
    }
    assert!(
        d.nu.iter()
            .all(|r| coordinates(&g, *r).iter().all(|v| v == "0"))
    );
    // Erasing the value encoding never changes the source types or admits cross-owner assignments.
    assert!(f.types().iter().any(|t| matches!(t, Type::Owned(..))));
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn parameter_columns_and_equal_functions_keep_every_original_index_and_required_generator() {
    let e = example(
        false,
        "law required grid(c:Part,n:Fp(2),b:Bool):c.quantity=n;",
    );
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(d.nu.len(), 4);
    assert_eq!(d.columns.len(), 4);
    assert_eq!(
        d.columns
            .iter()
            .copied()
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        4
    );
    assert_eq!(
        d.components
            .iter()
            .map(|(i, _)| *i)
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        1
    );
    assert!(
        d.components
            .iter()
            .all(|(_, p)| p.as_deref() == Some([].as_slice()))
    );
    let values = d.nu.iter().map(|r| coordinates(&g, *r)).collect::<Vec<_>>();
    assert_eq!(values.iter().filter(|v| **v == ["0", "1"]).count(), 2);
    assert_eq!(values.iter().filter(|v| **v == ["1", "0"]).count(), 2);
    let Part::Ideal {
        generators,
        required,
        ..
    } = data(&g, d.required).part()
    else {
        panic!("required")
    };
    assert!(*required);
    assert_eq!(generators, &d.nu);
    assert_eq!(d.witnesses.len(), 4);
    assert_eq!(
        d.nu.iter()
            .map(|r| r.0)
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        4
    );
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn fp11_public_domain_permutation_also_orders_nu_epsilon_and_evaluation_basis() {
    let definition = DEFINITION.replace(r#"["Fp","2"]"#, r#"["Fp","11"]"#);
    let map = MAP.replace(r#""value":"0""#, r#""value":"10""#);
    let e = evaluate_observed_bytes(
        custom_sources(&definition, &map, "law required two(c:Part):c.quantity=2;"),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &mut quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
        .unwrap()
        .unwrap();
    let Part::Domain { elements, .. } = data(&g, d.domain).part() else {
        panic!("D")
    };
    let values = elements
        .iter()
        .map(|r| match g.scalar(*r).unwrap() {
            Scalar::Fp { value, .. } => value.to_string(),
            _ => panic!("Fp11"),
        })
        .collect::<Vec<_>>();
    assert_eq!(
        values,
        ["0", "1", "10", "2", "3", "4", "5", "6", "7", "8", "9"]
    );
    assert_eq!(d.points, [0, 1, 10, 2, 3, 4, 5, 6, 7, 8, 9]);
    assert_eq!(
        coordinates(&g, d.nu[0]),
        ["1", "1", "1", "0", "1", "1", "1", "1", "1", "1", "1"]
    );
    assert_eq!(coordinates(&g, d.epsilon[0].unwrap()), vec!["1"; 11]);
    let Part::Evaluation { basis_images, .. } = data(&g, d.evaluation.unwrap()).part() else {
        panic!("evaluation")
    };
    assert_eq!(
        basis_images
            .iter()
            .map(|r| match g.scalar(*r).unwrap() {
                Scalar::Z(n) => n.to_string(),
                _ => panic!("Z"),
            })
            .collect::<Vec<_>>(),
        ["0", "0", "1", "0", "0", "0", "0", "0", "0", "0", "0"]
    );
    let Part::Ideal { generators, .. } = data(&g, d.required).part() else {
        panic!("ideal")
    };
    assert_eq!(generators, &d.nu);
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn set_fp11_domain_uses_recursive_canonical_values_and_keeps_point_evaluation() {
    let definition = DEFINITION.replace(r#"["Fp","2"]"#, r#"["Set",["Fp","11"]]"#);
    let map = MAP
        .replace(r#""value":"0""#, r#""value":["3","10"]"#)
        .replace(r#""value":"1""#, r#""value":["2"]"#);
    let e = evaluate_observed_bytes(
        custom_sources(
            &definition,
            &map,
            "law required reflexive(c:Part):c.quantity=c.quantity;",
        ),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &mut quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
        .unwrap()
        .unwrap();
    let Part::Domain { elements, .. } = data(&g, d.domain).part() else {
        panic!("D")
    };
    assert_eq!(elements.len(), 2048);
    // 独立した11 bitの集合入力から、原始encodingのUTF-8順を作る。
    let mut expected = (0..2048u16)
        .map(|mask| {
            let mut items = (0..11)
                .filter(|i| mask & (1 << i) != 0)
                .map(|i| format!("\"{i}\""))
                .collect::<Vec<_>>();
            items.sort();
            format!("[{}]", items.join(","))
        })
        .collect::<Vec<_>>();
    expected.sort();
    let actual = elements
        .iter()
        .map(|r| g.scalar(*r).unwrap().wire().canonical())
        .collect::<Vec<_>>();
    assert_eq!(actual, expected);
    let pair = actual.iter().position(|v| v == r#"["10","3"]"#).unwrap();
    let singleton = actual.iter().position(|v| v == r#"["2"]"#).unwrap();
    assert!(pair < singleton);
    assert_eq!(coordinates(&g, d.nu[0]), vec!["0"; 2048]);
    assert_eq!(coordinates(&g, d.epsilon[0].unwrap()), vec!["0"; 2048]);
    let Part::Evaluation { basis_images, .. } = data(&g, d.evaluation.unwrap()).part() else {
        panic!("evaluation")
    };
    for (point, r) in basis_images.iter().enumerate() {
        assert!(
            matches!(g.scalar(*r).unwrap(), Scalar::Z(n) if n == &if point == pair { 1.into() } else { 0.into() })
        );
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn nested_primitive_containers_canonicalize_sets_and_maps_but_preserve_sequences() {
    let fp = Type::Fp("11".into());
    let set = || Scalar::Set {
        element: fp.clone(),
        items: [3, 10]
            .into_iter()
            .map(|n| Scalar::Fp {
                modulus: "11".into(),
                value: n.into(),
            })
            .collect(),
    };
    let subject = |id: &str| Scalar::Subject {
        snapshot: "v".into(),
        subject: id.into(),
        entity: "Finite.Root".into(),
    };
    let value = Scalar::Tuple(vec![
        Scalar::List {
            element: Type::Set(Box::new(fp.clone())),
            items: vec![
                set(),
                Scalar::Set {
                    element: fp.clone(),
                    items: vec![Scalar::Fp {
                        modulus: "11".into(),
                        value: 2.into(),
                    }],
                },
            ],
        },
        Scalar::Option {
            element: Type::Set(Box::new(fp.clone())),
            value: Some(Box::new(set())),
        },
        Scalar::Data {
            family: "Finite.Container".into(),
            constructor: "Finite.Container.Pack".into(),
            args: vec![set()],
        },
        Scalar::Map {
            domain: Type::Ref("Finite.Root".into()),
            codomain: Type::Ref("Finite.Root".into()),
            pairs: vec![(subject("b"), subject("a")), (subject("a"), subject("b"))],
        },
    ]);
    let original = value.wire().canonical();
    let normalized = canonical_value(&value, &mut quiet()).unwrap();
    assert_eq!(normalized.ty(), value.ty());
    assert_eq!(
        normalized.wire().canonical(),
        r#"[[["10","3"],["2"]],{"some":["10","3"]},{"args":[["10","3"]],"tag":"Pack"},[[["v","a"],["v","b"]],[["v","b"],["v","a"]]]]"#
    );
    assert_eq!(value.wire().canonical(), original);
    assert_eq!(
        canonical_value(&normalized, &mut quiet()).unwrap(),
        normalized
    );
    for mode in 0..4 {
        for at in [1, 5, 10] {
            assert!(matches!(
                canonical_value(&value, &mut stopping(mode, at)),
                Err(ValidationFailure::Stop(_))
            ));
            assert_eq!(value.wire().canonical(), original);
        }
    }
}
