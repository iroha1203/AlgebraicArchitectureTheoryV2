use super::*;
use crate::{input::InputSources, observed::evaluate_observed_bytes};

use crate::control::quiet;
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
        // 原始代入上の表示と、補完せず実際に読んだBool値を区別する。
        let observed = matches!(data(&g, NodeRef(i)).part(), Part::ObservedBoolean { .. });
        assert_eq!(n.scope.assignments, !observed);
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
    let environment = Environment::new(e.prepared.inputs(), &mut quiet()).unwrap();
    assert!(matches!(
        environment.indexes.field(&environment.state, "v", "q", "Finite.Part.quantity")
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
fn stopping(signal: crate::result::Signal, at: usize) -> Control {
    let seen = std::rc::Rc::new(std::cell::Cell::new(0));
    Control::new(move |p| {
        if p == Checkpoint::FiniteLawFunction {
            seen.set(seen.get() + 1);
        }
        (seen.get() >= at).then_some(signal)
    })
}
#[test]
fn signal_stops_keep_unfinished_plan_private_and_preserve_completed_prefix_nodes() {
    let e = example(false, BODY);
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let before = g.nodes.len();
    let count = std::rc::Rc::new(std::cell::Cell::new(0));
    let seen = count.clone();
    let mut c = Control::new(move |p| {
        if p == Checkpoint::FiniteLawFunction {
            seen.set(seen.get() + 1);
        }
        None
    });
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut c)
        .unwrap()
        .unwrap();
    let source = data(&g, d.ring).source.clone();
    let total = count.get();
    assert!(total > 20);
    for signal in [crate::result::Signal::Int, crate::result::Signal::Term] {
        for at in [1, 5, total - 1, total] {
            let mut g = graph(&e);
            let a = architecture(&g, "a");
            assert!(matches!(
                retain(
                    &mut g,
                    e.prepared.shared_inputs(),
                    a,
                    0,
                    &mut stopping(signal, at)
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
                &mut stopping(signal, 1)
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
    let mut c = Control::new(move |_| flag.get().then_some(crate::result::Signal::Int));
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
                } = &env.indexes.field(&env.state, "v", subject, "Finite.Part.owner").unwrap().slot
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
fn set_fp5_domain_uses_recursive_canonical_values_and_keeps_point_evaluation() {
    let definition = DEFINITION.replace(r#"["Fp","2"]"#, r#"["Set",["Fp","5"]]"#);
    let map = MAP
        .replace(r#""value":"0""#, r#""value":["1","4"]"#)
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
    assert_eq!(elements.len(), 32);
    // 独立した5 bitの集合入力から、原始encodingのUTF-8順を作る。
    let mut expected = (0..32u16)
        .map(|mask| {
            let mut items = (0..5)
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
    let pair = actual.iter().position(|v| v == r#"["1","4"]"#).unwrap();
    let singleton = actual.iter().position(|v| v == r#"["2"]"#).unwrap();
    assert!(pair < singleton);
    assert_eq!(coordinates(&g, d.nu[0]), vec!["0"; 32]);
    assert_eq!(coordinates(&g, d.epsilon[0].unwrap()), vec!["0"; 32]);
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
    for signal in [crate::result::Signal::Int, crate::result::Signal::Term] {
        for at in [1, 5, 10] {
            assert!(matches!(
                canonical_value(&value, &mut stopping(signal, at)),
                Err(ValidationFailure::Stop(_))
            ));
            assert_eq!(value.wire().canonical(), original);
        }
    }
}

#[test]
fn full_parameter_rows_keep_original_roles_sources_and_all_four_scalar_assignments() {
    let body = "law required grid(c:Part,n:Fp(2),b:Bool) when b:let x=c.quantity in x=n;";
    let e = example(false, body);
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(d.originals.len(), 4);
    let mut assignments = std::collections::BTreeSet::new();
    for original in &d.originals {
        assert_eq!(
            original
                .bindings
                .iter()
                .map(|b| b.name.as_str())
                .collect::<Vec<_>>(),
            ["c", "n", "b"]
        );
        assert!(
            matches!(g.scalar(original.bindings[0].value).unwrap(), Scalar::Subject { snapshot, subject, entity } if snapshot=="v" && subject=="p" && entity=="Finite.Part")
        );
        let Scalar::Fp { value: n, .. } = g.scalar(original.bindings[1].value).unwrap() else {
            panic!("n")
        };
        let Scalar::Bool(b) = g.scalar(original.bindings[2].value).unwrap() else {
            panic!("b")
        };
        assignments.insert((n.to_string(), *b));
        let Part::LawInstance {
            column,
            original: instance,
            name,
            role,
            bindings,
            guard,
            body,
            ..
        } = data(&g, original.row).part()
        else {
            panic!("row")
        };
        assert_eq!(*column, original.column);
        assert_eq!(*instance, original.instance);
        assert_eq!(name, "Chosen.grid");
        assert_eq!(*role, Role::Required);
        assert_eq!(bindings, &original.bindings);
        assert_eq!(*body, original.body);
        assert_eq!(*guard, original.guard);
        assert!(guard.is_some());
        for r in [original.body, original.guard.unwrap()] {
            assert_eq!(g.get(r).unwrap().ty, NodeType::Expression(Type::Bool));
            assert_eq!(property(&g, r, "parameters"), Json::Arr(vec![]));
            assert_eq!(
                property(&g, r, "bindings"),
                property(&g, original.row, "bindings")
            );
            assert!(original.bindings.iter().all(|b| b.value.0 < r.0));
        }
        assert!(original.body.0 < original.row.0 && original.guard.unwrap().0 < original.row.0);
    }
    assert_eq!(
        assignments,
        [
            ("0".into(), false),
            ("0".into(), true),
            ("1".into(), false),
            ("1".into(), true)
        ]
        .into_iter()
        .collect()
    );
    // 元のArchitectureには未束縛のn,bが残り、有限rowで置き換えない。
    let origin = &data(&g, d.ring).source.architecture;
    let instance = &origin.readings().instances()[d.originals[0].instance];
    assert_eq!(
        instance
            .parameters()
            .iter()
            .map(|p| p.name.as_str())
            .collect::<Vec<_>>(),
        ["n", "b"]
    );
    assert!(
        d.originals
            .iter()
            .all(|r| r.instance == d.originals[0].instance)
    );
    assert_eq!(
        d.originals
            .iter()
            .map(|r| r.column)
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        4
    );
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn source_locations_keep_whole_let_match_and_guard_occurrences() {
    for source_body in ["let x=c.quantity in x=0", "match c.quantity{x=>x=0;}"] {
        let text = format!("law optional lexical(c:Part) when c.quantity=1:{source_body};");
        let e = example(false, &text);
        let raw = std::str::from_utf8(e.prepared.inputs().sources().law().bytes()).unwrap();
        let mut g = graph(&e);
        let a = architecture(&g, "a");
        let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
            .unwrap()
            .unwrap();
        assert_eq!(d.originals.len(), 1);
        let row = &d.originals[0];
        let start = raw.find(source_body).unwrap();
        assert_eq!(
            property(&g, row.body, "location"),
            location_wire(&Location::Law {
                span: (start, start + source_body.len())
            })
        );
        let guard_start = raw.find("c.quantity=1").unwrap();
        assert_eq!(
            property(&g, row.guard.unwrap(), "location"),
            location_wire(&Location::Law {
                span: (guard_start, guard_start + "c.quantity=1".len())
            })
        );
        assert_eq!(property(&g, row.row, "role"), Json::str("optional"));
        assert_eq!(property(&g, row.row, "body"), row.body.wire());
        assert_eq!(property(&g, row.row, "guard"), row.guard.unwrap().wire());
        let declaration_start = raw.find("law optional lexical").unwrap();
        assert_eq!(
            property(&g, row.row, "occurrence"),
            location_wire(&Location::Law {
                span: (declaration_start, declaration_start + text.len())
            })
        );
        replay(&e, &g.nodes, &g.contexts).unwrap();
    }
}

#[test]
fn original_source_rows_survive_missing_observation_and_preserve_unconditional_omission() {
    let e = example(true, BODY);
    let mut g = graph(&e);
    let b = architecture(&g, "b");
    let d = retain(&mut g, e.prepared.shared_inputs(), b, 0, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(d.originals.len(), 2);
    assert!(d.evaluation.is_none());
    assert!(d.epsilon.iter().all(Option::is_none));
    let mut roles = vec![];
    for row in &d.originals {
        assert!(row.guard.is_none());
        assert!(!matches!(wire(&g, row.row),Json::Obj(ref o) if o.contains_key("guard")));
        assert_eq!(property(&g, row.body, "kind"), Json::str("source"));
        assert!(
            matches!(g.scalar(row.bindings[0].value).unwrap(), Scalar::Subject { subject, .. } if subject=="q")
        );
        roles.push((property(&g, row.row, "name"), property(&g, row.row, "role")));
    }
    assert_eq!(
        roles,
        vec![
            (Json::str("Chosen.one"), Json::str("optional")),
            (Json::str("Chosen.zero"), Json::str("required"))
        ]
    );
    let Part::Domain { elements, .. } = data(&g, d.domain).part() else {
        panic!("D")
    };
    assert_eq!(elements.len(), 2);
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn full_law_rows_reject_original_column_bindings_role_expression_and_output_tampering() {
    let e = example(
        false,
        "law required grid(c:Part,n:Fp(2),b:Bool) when b:c.quantity=n;",
    );
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
        .unwrap()
        .unwrap();
    let source = data(&g, d.ring).source.clone();
    let first = &d.originals[0];
    for mode in 0..10 {
        let mut changed = (*source).clone();
        match mode {
            0 => changed.outputs.originals.reverse(),
            1 => {
                if let Part::Source { column, .. } = &mut changed.parts[first.body.0 - source.base]
                {
                    *column = usize::MAX;
                }
            }
            2 => {
                if let Part::Source { expression, .. } =
                    &mut changed.parts[first.body.0 - source.base]
                {
                    *expression = usize::MAX;
                }
            }
            3 => {
                if let Part::Source { location, .. } =
                    &mut changed.parts[first.body.0 - source.base]
                {
                    *location = Location::Law { span: (0, 1) };
                }
            }
            4 => {
                if let Part::Source { bindings, .. } =
                    &mut changed.parts[first.body.0 - source.base]
                {
                    bindings.swap(0, 1);
                }
            }
            5 => {
                if let Part::LawInstance { role, .. } =
                    &mut changed.parts[first.row.0 - source.base]
                {
                    *role = Role::Optional;
                }
            }
            6 => {
                if let Part::LawInstance { name, .. } =
                    &mut changed.parts[first.row.0 - source.base]
                {
                    *name = "Chosen.other".into();
                }
            }
            7 => {
                if let Part::LawInstance { body, guard, .. } =
                    &mut changed.parts[first.row.0 - source.base]
                {
                    *body = guard.unwrap();
                }
            }
            9 => {
                if let Part::LawInstance { original, .. } =
                    &mut changed.parts[first.row.0 - source.base]
                {
                    *original = usize::MAX;
                }
            }
            _ => {
                if let Part::Scalar(Scalar::Fp { value, .. }) =
                    &mut changed.parts[first.bindings[1].value.0 - source.base]
                {
                    *value = if *value == 0.into() {
                        1.into()
                    } else {
                        0.into()
                    };
                }
            }
        }
        assert!(
            changed
                .recheck(e.prepared.inputs(), &source.architecture, 0, &mut quiet())
                .is_err(),
            "mode {mode}"
        );
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn empty_law_family_keeps_no_fabricated_original_source_rows() {
    let e = example(false, "");
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
        .unwrap()
        .unwrap();
    assert!(d.originals.is_empty());
    assert!(
        !data(&g, d.ring)
            .source
            .parts
            .iter()
            .any(|p| matches!(p, Part::Source { .. } | Part::LawInstance { .. }))
    );
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

fn expression_free_parameters(g: &Graph, r: NodeRef) -> std::collections::BTreeSet<String> {
    match data(g, r).part() {
        Part::Source { parameters, .. } => parameters.iter().map(|p| p.0.clone()).collect(),
        Part::Transform {
            operation: Transform::Substitute,
            operands,
            bindings,
            ..
        } => {
            let mut free = expression_free_parameters(g, operands[0]);
            for b in bindings {
                assert!(free.remove(&b.name));
                assert_eq!(
                    g.get(b.value).unwrap().ty,
                    NodeType::Expression(b.ty.clone())
                );
                free.extend(expression_free_parameters(g, b.value));
            }
            free
        }
        Part::Transform { operands, .. } => operands
            .iter()
            .flat_map(|r| expression_free_parameters(g, *r))
            .collect(),
        Part::Scalar(_) => Default::default(),
        _ => panic!("expression"),
    }
}
fn operand_source_texts(g: &Graph, r: NodeRef, law: &str) -> Vec<String> {
    let mut result = vec![];
    let mut pending = vec![r];
    while let Some(r) = pending.pop() {
        if let Part::Source {
            location: Location::Law { span },
            ..
        } = data(g, r).part()
        {
            result.push(law[span.0..span.1].to_owned());
        }
        pending.extend(data(g, r).part().arguments());
    }
    result
}
#[test]
fn direct_equation_operands_keep_original_types_locations_and_coordinate_order() {
    let e = example(false, BODY);
    let raw = std::str::from_utf8(e.prepared.inputs().sources().law().bytes()).unwrap();
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(d.operands.len(), 2);
    for (index, (left, right)) in d.operands.iter().enumerate() {
        assert_eq!(
            g.get(*left).unwrap().ty,
            NodeType::Expression(Type::Fp("2".into()))
        );
        assert_eq!(
            g.get(*right).unwrap().ty,
            NodeType::Expression(Type::Fp("2".into()))
        );
        assert_eq!(operand_source_texts(&g, *left, raw), ["c.quantity"]);
        assert_eq!(
            operand_source_texts(&g, *right, raw),
            [if index == 0 { "1" } else { "0" }]
        );
        assert!(expression_free_parameters(&g, *left).is_empty());
        assert!(expression_free_parameters(&g, *right).is_empty());
        assert_eq!(property(&g, *left, "parameters"), Json::Arr(vec![]));
        assert_eq!(
            property(&g, *left, "bindings"),
            property(&g, d.originals[index].body, "bindings")
        );
        assert_eq!(d.columns[index], d.originals[index].column);
        assert_eq!(d.components[index].0, d.originals[index].instance);
    }
    assert_eq!(coordinates(&g, d.nu[0]), ["1", "0"]);
    assert_eq!(coordinates(&g, d.nu[1]), ["0", "1"]);
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn lexical_operand_substitution_closes_nested_let_match_and_keeps_discarded_reads() {
    for (body, names, nu) in [
        (
            "let x=c.quantity in let y=x+1 in y=0",
            vec!["x", "y"],
            vec!["1", "0"],
        ),
        (
            "match c.quantity{x=>let y=x+1 in y=0;}",
            vec!["x", "y"],
            vec!["1", "0"],
        ),
        (
            "let unused=c.quantity in c.quantity=0",
            vec!["unused"],
            vec!["0", "1"],
        ),
        ("match c.quantity{_=>c.quantity=0;}", vec![], vec!["0", "1"]),
        (
            "let unused=c.quantity in 0=0",
            vec!["unused"],
            vec!["0", "0"],
        ),
        ("match c.quantity{_=>0=0;}", vec![], vec!["0", "0"]),
    ] {
        let e = example(false, &format!("law required lexical(c:Part):{body};"));
        let raw = std::str::from_utf8(e.prepared.inputs().sources().law().bytes()).unwrap();
        let mut g = graph(&e);
        let a = architecture(&g, "a");
        let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
            .unwrap()
            .unwrap();
        let (left, right) = d.operands[0];
        assert!(expression_free_parameters(&g, left).is_empty());
        assert!(expression_free_parameters(&g, right).is_empty());
        assert_eq!(coordinates(&g, d.nu[0]), nu);
        assert!(
            g.get(left)
                .unwrap()
                .support
                .iter()
                .any(|f| f.atom.as_deref() == Some("px"))
        );
        let texts = operand_source_texts(&g, left, raw);
        if body != "match c.quantity{_=>0=0;}" {
            assert!(texts.iter().any(|s| s == "c.quantity"));
        } else {
            assert_eq!(texts, ["0"]);
        }
        let Part::Domain { elements, .. } = data(&g, d.domain).part() else {
            panic!("D")
        };
        assert_eq!(elements.len(), 2);
        if !names.is_empty() {
            let Part::Transform {
                operation: Transform::Substitute,
                bindings,
                operands,
                ..
            } = data(&g, left).part()
            else {
                panic!("closed")
            };
            assert_eq!(
                bindings.iter().map(|b| b.name.as_str()).collect::<Vec<_>>(),
                names
            );
            assert_eq!(property(&g, left, "operation"), Json::str("substitute"));
            assert_eq!(property(&g, left, "operands"), refs(operands));
            let Part::Source { parameters, .. } = data(&g, operands[0]).part() else {
                panic!("source")
            };
            assert_eq!(
                parameters.iter().map(|p| p.0.as_str()).collect::<Vec<_>>(),
                names
            );
        }
        if names == ["x", "y"] {
            assert!(texts.iter().any(|s| s == "x+1"));
            assert!(texts.iter().any(|s| s == "y"));
        }
        let start = raw.find(body).unwrap();
        assert_eq!(
            property(&g, d.originals[0].body, "location"),
            location_wire(&Location::Law {
                span: (start, start + body.len())
            })
        );
        replay(&e, &g.nodes, &g.contexts).unwrap();
    }
}
#[test]
fn tuple_operand_components_project_closed_sources_with_matching_types_and_values() {
    let definition = DEFINITION.replace(r#"["Fp","2"]"#, r#"["Tuple",["Fp","2"],"Bool"]"#);
    let map = MAP
        .replace(r#""value":"0""#, r#""value":["0",true]"#)
        .replace(r#""value":"1""#, r#""value":["1",false]"#);
    let e = evaluate_observed_bytes(
        custom_sources(
            &definition,
            &map,
            "law required pair(c:Part):let t=c.quantity in t=(0,true);",
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
    assert_eq!(d.operands.len(), 2);
    for (component, (left, right)) in d.operands.iter().enumerate() {
        let expected = if component == 0 {
            Type::Fp("2".into())
        } else {
            Type::Bool
        };
        for r in [left, right] {
            assert_eq!(
                g.get(*r).unwrap().ty,
                NodeType::Expression(expected.clone())
            );
            assert_eq!(property(&g, *r, "operation"), Json::str("project"));
            assert_eq!(property(&g, *r, "position"), Json::Nat(component as u64));
            assert!(expression_free_parameters(&g, *r).is_empty());
            let Part::Transform { operands, .. } = data(&g, *r).part() else {
                panic!("project")
            };
            assert_eq!(
                property(&g, operands[0], "operation"),
                Json::str("substitute")
            );
        }
        assert_eq!(d.components[component].1, Some(vec![component]));
    }
    assert_eq!(coordinates(&g, d.nu[0]), ["0", "0", "1", "1"]);
    assert_eq!(coordinates(&g, d.nu[1]), ["1", "0", "1", "0"]);
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn general_boolean_conditions_keep_the_body_and_fixed_unit_equality_truth() {
    let e = example(
        false,
        "law required no(c:Part):false;law optional yes(c:Part):true;",
    );
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(d.operands.len(), 2);
    for (index, (left, right)) in d.operands.iter().enumerate() {
        assert_eq!(*left, d.originals[index].body);
        assert_eq!(g.get(*left).unwrap().ty, NodeType::Expression(Type::Bool));
        assert_eq!(g.get(*right).unwrap().ty, NodeType::Expression(Type::Bool));
        let Part::Transform {
            operation: Transform::Equal,
            operands,
            bindings,
            position,
            ..
        } = data(&g, *right).part()
        else {
            panic!("truth")
        };
        assert!(bindings.is_empty() && position.is_none());
        assert_eq!(operands.len(), 2);
        assert_eq!(operands[0], operands[1]);
        assert!(matches!(g.scalar(operands[0]).unwrap(), Scalar::Unit));
        assert_eq!(property(&g, *right, "operation"), Json::str("equal"));
        assert!(expression_free_parameters(&g, *right).is_empty());
        assert_eq!(d.components[index].1, None);
    }
    assert_eq!(coordinates(&g, d.nu[0]), ["1"]);
    assert_eq!(coordinates(&g, d.nu[1]), ["0"]);
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn operand_plans_reject_free_parameter_substitution_type_projection_and_output_changes() {
    let definition = DEFINITION.replace(r#"["Fp","2"]"#, r#"["Tuple",["Fp","2"],"Bool"]"#);
    let map = MAP
        .replace(r#""value":"0""#, r#""value":["0",true]"#)
        .replace(r#""value":"1""#, r#""value":["1",false]"#);
    let e = evaluate_observed_bytes(
        custom_sources(
            &definition,
            &map,
            "law required pair(c:Part):let t=c.quantity in t=(0,true);",
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
    let source = data(&g, d.ring).source.clone();
    let project = d.operands[0].0.0 - source.base;
    let Part::Transform { operands, .. } = &source.parts[project] else {
        panic!("project")
    };
    let substitute = operands[0].0 - source.base;
    let Part::Transform { operands, .. } = &source.parts[substitute] else {
        panic!("substitute")
    };
    let open = operands[0].0 - source.base;
    for mode in 0..6 {
        let mut changed = (*source).clone();
        match mode {
            0 => changed.outputs.operands.reverse(),
            1 => {
                if let Part::Transform { position, .. } = &mut changed.parts[project] {
                    *position = Some(usize::MAX);
                }
            }
            2 => {
                if let Part::Transform { ty, .. } = &mut changed.parts[project] {
                    *ty = Type::Unit;
                }
            }
            3 => {
                if let Part::Transform { bindings, .. } = &mut changed.parts[substitute] {
                    bindings.clear();
                }
            }
            4 => {
                if let Part::Transform { bindings, .. } = &mut changed.parts[substitute] {
                    bindings[0].name = "other".into();
                }
            }
            _ => {
                if let Part::Source { parameters, .. } = &mut changed.parts[open] {
                    parameters.clear();
                }
            }
        }
        assert!(
            changed
                .recheck(e.prepared.inputs(), &source.architecture, 0, &mut quiet())
                .is_err(),
            "mode {mode}"
        );
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn all_four_stops_inside_operand_construction_leave_original_graph_and_source_unchanged() {
    let e = example(
        false,
        "law required lexical(c:Part):let x=c.quantity in let y=x+1 in y=0;",
    );
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
        .unwrap()
        .unwrap();
    let source = data(&g, d.ring).source.clone();
    let full = finite_automatic_law_family(
        e.prepared.inputs(),
        source.architecture.readings(),
        &mut quiet(),
    )
    .unwrap();
    let f = full.family().unwrap();
    let count = std::rc::Rc::new(std::cell::Cell::new(0));
    let seen = count.clone();
    let mut control = Control::new(move |p| {
        if p == Checkpoint::FiniteLawFunction {
            seen.set(seen.get() + 1);
        }
        None
    });
    let mut parts = source.parts.clone();
    operands::append(
        f,
        e.prepared.inputs(),
        &d.originals,
        &d.columns,
        &d.components,
        &mut parts,
        source.base,
        &mut control,
    )
    .unwrap();
    let total = count.get();
    assert!(total > 10);
    let before = g.nodes.len();
    for signal in [crate::result::Signal::Int, crate::result::Signal::Term] {
        for at in [1, 5, total / 2, total] {
            let mut parts = source.parts.clone();
            assert!(matches!(
                operands::append(
                    f,
                    e.prepared.inputs(),
                    &d.originals,
                    &d.columns,
                    &d.components,
                    &mut parts,
                    source.base,
                    &mut stopping(signal, at)
                ),
                Err(ValidationFailure::Stop(_))
            ));
            assert_eq!(g.nodes.len(), before);
            assert_eq!(data(&g, d.ring).source.parts, source.parts);
        }
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn missing_operand_values_keep_closed_source_expressions_without_fabricated_scalar_results() {
    let e = example(true, BODY);
    let raw = std::str::from_utf8(e.prepared.inputs().sources().law().bytes()).unwrap();
    let mut g = graph(&e);
    let b = architecture(&g, "b");
    let d = retain(&mut g, e.prepared.shared_inputs(), b, 0, &mut quiet())
        .unwrap()
        .unwrap();
    assert!(d.evaluation.is_none() && d.epsilon.iter().all(Option::is_none));
    assert_eq!(d.operands.len(), 2);
    for (left, right) in &d.operands {
        assert_eq!(
            g.get(*left).unwrap().ty,
            NodeType::Expression(Type::Fp("2".into()))
        );
        assert_eq!(
            g.get(*right).unwrap().ty,
            NodeType::Expression(Type::Fp("2".into()))
        );
        assert!(g.scalar(*left).is_err() && g.scalar(*right).is_err());
        assert!(expression_free_parameters(&g, *left).is_empty());
        assert_eq!(operand_source_texts(&g, *left, raw), ["c.quantity"]);
        assert!(
            !g.get(*left)
                .unwrap()
                .support
                .iter()
                .any(|f| f.atom.as_deref() == Some("qx"))
        );
        let Part::Source { bindings, .. } = data(&g, *left).part() else {
            panic!("source")
        };
        assert!(
            matches!(g.scalar(bindings[0].value).unwrap(),Scalar::Subject{subject,..}if subject=="q")
        );
    }
    assert_eq!(coordinates(&g, d.nu[0]), ["1", "0"]);
    assert_eq!(coordinates(&g, d.nu[1]), ["0", "1"]);
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn finite_equation_presentation_connects_original_rows_operands_ideals_and_full_context() {
    use crate::observed::equation_presentation_node::Part as E;
    let e = example(false, BODY);
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
        .unwrap()
        .unwrap();
    let ctx = d.context.unwrap();
    let presentation = d.presentation.unwrap();
    let Part::Equation(E::Context {
        base,
        carrier,
        dependencies,
        laws,
        ..
    }) = data(&g, ctx).part()
    else {
        panic!("context");
    };
    assert_eq!(*base, a);
    assert_eq!(carrier.len(), 12);
    let decoded = carrier
        .iter()
        .map(|v| {
            let Scalar::Tuple(xs) = v else {
                panic!("identity");
            };
            assert_eq!(xs.len(), 4);
            let (
                Scalar::Text(s),
                Scalar::Text(id),
                Scalar::Option { value: field, .. },
                Scalar::Option { value: atom, .. },
            ) = (&xs[0], &xs[1], &xs[2], &xs[3])
            else {
                panic!("identity fields");
            };
            (
                s.clone(),
                id.clone(),
                field.as_ref().map(|f| f.wire().canonical()),
                atom.as_ref().map(|a| a.wire().canonical()),
            )
        })
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(decoded.len(), 12);
    for id in ["a", "b", "p", "q", "m"] {
        assert!(decoded.contains(&("v".into(), id.into(), None, None)));
    }
    assert!(decoded.contains(&(
        "v".into(),
        "p".into(),
        Some(Json::str("Finite.Part.quantity").canonical()),
        Some(Json::str("px").canonical())
    )));
    assert!(dependencies.iter().any(|(r,f)|f=="Finite.Part.quantity" && matches!(g.scalar(*r).unwrap(),Scalar::Subject{snapshot,subject,..} if snapshot=="v"&&subject=="p")));
    assert_eq!(laws, &d.originals.iter().map(|o| o.row).collect::<Vec<_>>());
    let Part::Equation(E::Presentation {
        instances,
        domain,
        ring,
        coordinates,
        witnesses,
        required,
        evaluation,
        context,
        ..
    }) = data(&g, presentation).part()
    else {
        panic!("presentation");
    };
    assert_eq!(instances, laws);
    assert_eq!(
        (*domain, *ring, *required, *evaluation, *context),
        (d.domain, d.ring, d.required, d.evaluation, ctx)
    );
    assert_eq!(witnesses, &d.witnesses);
    assert_eq!(coordinates.len(), d.nu.len());
    for (i, q) in coordinates.iter().enumerate() {
        assert_eq!(q.nu, d.nu[i]);
        assert_eq!(q.epsilon, d.epsilon[i]);
        assert_eq!((q.lhs, q.rhs), d.operands[i]);
        assert!(instances.contains(&q.instance));
        assert!(q.component.is_empty());
    }
    assert_eq!(g.get(ctx).unwrap().ty, NodeType::Construction(T::Context));
    assert_eq!(
        g.get(presentation).unwrap().ty,
        NodeType::Construction(T::EquationPresentation)
    );
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn finite_presentation_does_not_invent_evaluation_and_rejects_context_and_coordinate_changes() {
    use crate::observed::equation_presentation_node::Part as E;
    let e = example(true, BODY);
    let mut g = graph(&e);
    let a = architecture(&g, "b");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet())
        .unwrap()
        .unwrap();
    let r = d.presentation.unwrap();
    let Part::Equation(E::Presentation { evaluation, .. }) = data(&g, r).part() else {
        panic!("presentation");
    };
    assert!(evaluation.is_none());
    let reasons = &g.nodes[r.0].reasons;
    assert_eq!(reasons.len(), 1);
    assert_eq!(reasons[0].kind, ReasonKind::Missing);
    assert_eq!(reasons[0].request, "m");
    assert_eq!(
        reasons[0].missing,
        vec![Fact {
            snapshot: "v".into(),
            subject: "q".into(),
            field: Some("Finite.Part.quantity".into()),
            atom: None
        }]
    );
    let mut expected = d
        .originals
        .iter()
        .flat_map(|o| std::iter::once(o.body).chain(o.guard))
        .collect::<Vec<_>>();
    expected.sort_by_key(|r| r.0);
    expected.dedup();
    assert_eq!(reasons[0].dependencies, expected);
    assert!(
        reasons[0]
            .dependencies
            .iter()
            .all(|r| matches!(g.nodes[r.0].ty, NodeType::Expression(_)))
    );
    for kind in 0..3 {
        let mut nodes = g.nodes.clone();
        match kind {
            0 => nodes[r.0].reasons.clear(),
            1 => nodes[r.0].reasons[0].missing[0].field = Some("Finite.Part.owner".into()),
            _ => nodes[r.0].reasons[0].dependencies = vec![a],
        }
        assert!(
            replay(&e, &nodes, &g.contexts).is_err(),
            "missing reason change {kind}"
        );
    }
    for kind in 0..7 {
        let at = if kind < 3 { d.context.unwrap() } else { r };
        let mut nodes = g.nodes.clone();
        let Some(Payload::Construction(v)) = &mut nodes[at.0].payload else {
            panic!("native");
        };
        let D::FiniteLaw(value) = &mut v.data else {
            panic!("finite");
        };
        let mut source = (*value.source).clone();
        let Part::Equation(part) = &mut source.parts[value.index] else {
            panic!("equation");
        };
        match part {
            E::Context {
                base,
                carrier,
                laws,
                ..
            } => match kind {
                0 => {
                    carrier.pop();
                }
                1 => *base = d.domain,
                _ => laws.clear(),
            },
            E::Presentation {
                coordinates,
                ring,
                required,
                context,
                ..
            } => match kind {
                3 => coordinates[0].component = vec![1],
                4 => *ring = *required,
                5 => {
                    let q = &mut coordinates[0];
                    std::mem::swap(&mut q.lhs, &mut q.rhs)
                }
                _ => *context = a,
            },
        }
        value.source = Arc::new(source);
        assert!(replay(&e, &nodes, &g.contexts).is_err(), "change {kind}");
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn context_and_presentation_node_stops_keep_exact_finished_prefixes_for_all_four_reasons() {
    let e = example(false, BODY);
    let mut complete = graph(&e);
    let a = architecture(&complete, "a");
    let before = complete.nodes.len();
    let d = retain(
        &mut complete,
        e.prepared.shared_inputs(),
        a,
        0,
        &mut quiet(),
    )
    .unwrap()
    .unwrap();
    let context = d.context.unwrap();
    let presentation = d.presentation.unwrap();
    for signal in [crate::result::Signal::Int, crate::result::Signal::Term] {
        for at in [
            2 * (context.0 - before) + 1,
            2 * (context.0 - before + 1),
            2 * (presentation.0 - before + 1),
        ] {
            let seen = std::rc::Rc::new(std::cell::Cell::new(0));
            let count = seen.clone();
            let mut control = Control::new(move |point| {
                if point == Checkpoint::NativeResultNode {
                    count.set(count.get() + 1);
                }
                (count.get() >= at).then_some(signal)
            });
            let old = graph(&e);
            let mut g = Graph::new(&control);
            g.nodes = old.nodes;
            g.contexts = old.contexts;
            g.frames = old.frames;
            g.iterations = old.iterations;
            g.instances = old.instances;
            g.cases = old.cases;
            g.universal_witnesses = old.universal_witnesses;
            g.active = old.active;
            g.requests = old.requests;
            g.checked_answers = old.checked_answers;
            assert!(matches!(
                retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut control),
                Err(ValidationFailure::Stop(_))
            ));
            assert!(control.stop_reason().is_some());
            // 保持前checkpointで停止しても、計算済みnative nodeの転記は完了する。
            let expected = before + at.div_ceil(2);
            assert_eq!(g.nodes.len(), expected);
            assert_eq!(g.nodes.len(), g.contexts.len());
            for (current, normal) in g.nodes.iter().zip(&complete.nodes) {
                assert_eq!(
                    (
                        &current.ty,
                        &current.rule,
                        &current.arguments,
                        &current.support,
                        &current.scope,
                        &current.reasons,
                        &current.evidence,
                        &current.judgment
                    ),
                    (
                        &normal.ty,
                        &normal.rule,
                        &normal.arguments,
                        &normal.support,
                        &normal.scope,
                        &normal.reasons,
                        &normal.evidence,
                        &normal.judgment
                    )
                );
                match (&current.payload, &normal.payload) {
                    (Some(Payload::Construction(a)), Some(Payload::Construction(b))) => {
                        assert_eq!(a.wire(), b.wire())
                    }
                    _ => assert_eq!(current, normal),
                }
            }
            if at == 2 * (context.0 - before + 1) {
                assert_eq!(
                    g.get(context).unwrap().ty,
                    NodeType::Construction(T::Context)
                );
                assert!(g.get(presentation).is_err());
            }
            if at == 2 * (presentation.0 - before + 1) {
                assert_eq!(
                    g.get(presentation).unwrap().ty,
                    NodeType::Construction(T::EquationPresentation)
                );
            }
            replay(&e, &g.nodes, &g.contexts).unwrap();
        }
    }
}

#[test]
fn missing_self_equality_keeps_fiber_constant_without_presenting_an_observed_epsilon() {
    use crate::observed::equation_presentation_node::Part as E;
    let e = example(
        true,
        "law required self_equal(c:Part):c.quantity=c.quantity;",
    );
    let mut g = graph(&e);
    let b = architecture(&g, "b");
    let d = retain(&mut g, e.prepared.shared_inputs(), b, 0, &mut quiet())
        .unwrap()
        .unwrap();
    assert!(d.evaluation.is_none());
    assert_eq!(d.epsilon.len(), 1);
    assert_eq!(coordinates(&g, d.nu[0]), ["0", "0"]);
    assert_eq!(coordinates(&g, d.epsilon[0].unwrap()), ["0", "0"]);
    let at = d.presentation.unwrap();
    let Part::Equation(E::Presentation {
        coordinates: qs,
        evaluation,
        ..
    }) = data(&g, at).part()
    else {
        panic!("presentation")
    };
    assert!(evaluation.is_none());
    assert_eq!(qs.len(), 1);
    assert!(qs[0].epsilon.is_none());
    assert_eq!(qs[0].nu, d.nu[0]);
    assert_eq!((qs[0].lhs, qs[0].rhs), d.operands[0]);
    let reasons = &g.nodes[at.0].reasons;
    assert_eq!(reasons.len(), 1);
    assert_eq!(reasons[0].kind, ReasonKind::Missing);
    assert_eq!(reasons[0].missing[0].subject, "q");
    assert_eq!(
        reasons[0].missing[0].field.as_deref(),
        Some("Finite.Part.quantity")
    );
    assert!(reasons[0].missing[0].atom.is_none());
    let mut nodes = g.nodes.clone();
    let Some(Payload::Construction(v)) = &mut nodes[at.0].payload else {
        panic!("native")
    };
    let D::FiniteLaw(value) = &mut v.data else {
        panic!("finite")
    };
    let mut source = (*value.source).clone();
    let Part::Equation(E::Presentation { coordinates, .. }) = &mut source.parts[value.index] else {
        panic!("presentation")
    };
    coordinates[0].epsilon = d.epsilon[0];
    value.source = Arc::new(source);
    assert!(replay(&e, &nodes, &g.contexts).is_err());
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn an_unrelated_missing_finite_row_does_not_erase_an_observed_constant_row() {
    use crate::observed::equation_presentation_node::Part as E;
    for missing in [false, true] {
        let e = example(
            missing,
            "law required self_equal(c:Part):c.quantity=c.quantity;law required constant(c:Part):0=0;",
        );
        let mut g = graph(&e);
        let b = architecture(&g, "b");
        let d = retain(&mut g, e.prepared.shared_inputs(), b, 0, &mut quiet())
            .unwrap()
            .unwrap();
        let Part::Equation(E::Presentation {
            coordinates: qs,
            evaluation,
            ..
        }) = data(&g, d.presentation.unwrap()).part()
        else {
            panic!("presentation")
        };
        assert_eq!(evaluation.is_none(), missing);
        assert_eq!(qs.len(), 2);
        for (i, q) in qs.iter().enumerate() {
            let Part::LawInstance { name, .. } = data(&g, q.instance).part() else {
                panic!("instance")
            };
            assert_eq!(q.epsilon.is_some(), !missing || name == "Chosen.constant");
            assert_eq!(q.nu, d.nu[i]);
            if let Some(epsilon) = q.epsilon {
                assert_eq!(Some(epsilon), d.epsilon[i]);
                assert_eq!(coordinates(&g, epsilon), ["0", "0"]);
            }
        }
        replay(&e, &g.nodes, &g.contexts).unwrap();
    }
}

#[test]
fn a_false_finite_guard_does_not_turn_missing_operands_into_observations() {
    use crate::observed::equation_presentation_node::Part as E;
    for missing in [false, true] {
        let e = example(
            missing,
            "law required guarded(c:Part) when false:c.quantity=c.quantity;",
        );
        let mut g = graph(&e);
        let b = architecture(&g, "b");
        let d = retain(&mut g, e.prepared.shared_inputs(), b, 0, &mut quiet())
            .unwrap()
            .unwrap();
        assert!(d.epsilon.iter().all(Option::is_some));
        let Part::Equation(E::Presentation {
            coordinates: qs,
            evaluation,
            ..
        }) = data(&g, d.presentation.unwrap()).part()
        else {
            panic!("presentation")
        };
        assert_eq!(qs.len(), 1);
        assert_eq!(qs[0].epsilon.is_none(), missing);
        assert_eq!(evaluation.is_none(), missing);
        assert!(d.evaluation.is_some());
        assert_eq!(coordinates(&g, d.nu[0]), ["0"]);
        if missing {
            assert!(
                g.nodes[d.presentation.unwrap().0]
                    .reasons
                    .iter()
                    .any(|r| r.kind == ReasonKind::Missing
                        && r.missing.iter().any(|f| f.subject == "q"
                            && f.field.as_deref() == Some("Finite.Part.quantity")
                            && f.atom.is_none()))
            );
        }
        if let Some(epsilon) = qs[0].epsilon {
            assert!(coordinates(&g, epsilon).iter().all(|v| v == "0"));
        }
        replay(&e, &g.nodes, &g.contexts).unwrap();
    }
}
