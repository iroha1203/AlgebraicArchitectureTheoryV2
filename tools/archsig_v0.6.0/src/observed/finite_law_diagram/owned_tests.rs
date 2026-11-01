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
use crate::observed::object_component_diagram as objects;
fn family(e: &ObservedEvaluation, g: &mut Graph, name: &str) -> objects::Diagram {
    let a = architecture(g, name);
    objects::retain(g, e.prepared.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap()
}
#[test]
fn actual_owned_architectures_keep_containing_roots_and_distinct_observed_evaluations() {
    let e = example(false, BODY);
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let b = architecture(&g, "b");
    let fa = family(&e, &mut g, "a");
    let fb = family(&e, &mut g, "b");
    assert_eq!(fa.architectures[0], a);
    assert_eq!(fb.architectures[0], b);
    let p = retain(
        &mut g,
        e.prepared.shared_inputs(),
        fa.architectures[1],
        1,
        &mut quiet(),
    )
    .unwrap()
    .unwrap();
    let q = retain(
        &mut g,
        e.prepared.shared_inputs(),
        fb.architectures[1],
        1,
        &mut quiet(),
    )
    .unwrap()
    .unwrap();
    for (d, consumer, root, observed) in [
        (&p, fa.architectures[1], "a", "0"),
        (&q, fb.architectures[1], "b", "1"),
    ] {
        let source = &data(&g, d.ring).source;
        assert_eq!(source.reference, consumer);
        assert_eq!(source.object, 1);
        assert_eq!(source.architecture.construction().root().subject, root);
        assert_eq!(source.architecture.construction().reading(), "Chosen");
        assert_eq!(g.nodes[d.ring.0].arguments[0], consumer);
        assert_eq!(coordinates(&g, d.nu[0]), ["1", "0"]);
        assert_eq!(coordinates(&g, d.nu[1]), ["0", "1"]);
        assert_eq!(coordinates(&g, d.epsilon[1].unwrap()), [observed, observed]);
        assert_eq!(property(&g, d.required, "kind"), Json::str("obstruction"));
        let Part::Evaluation { basis_images, .. } = data(&g, d.evaluation.unwrap()).part() else {
            panic!("evaluation")
        };
        let images = basis_images
            .iter()
            .map(|r| match g.scalar(*r).unwrap() {
                Scalar::Z(n) => n.to_string(),
                _ => panic!("Z"),
            })
            .collect::<Vec<_>>();
        assert_eq!(
            images,
            if observed == "0" {
                vec!["1", "0"]
            } else {
                vec!["0", "1"]
            }
        );
        assert!(d.originals.iter().all(|o| o.bindings.iter().any(|b| matches!(g.scalar(b.value).unwrap(),Scalar::Subject{subject,..} if subject==if root=="a" {"p"} else {"q"}))));
    }
    assert!(!Arc::ptr_eq(
        &data(&g, p.ring).source.architecture,
        &data(&g, q.ring).source.architecture
    ));
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn base_and_owned_consumers_keep_identity_even_when_their_finite_values_agree() {
    let e = example(false, BODY);
    let mut g = graph(&e);
    let f = family(&e, &mut g, "a");
    let base = retain(
        &mut g,
        e.prepared.shared_inputs(),
        f.architectures[0],
        0,
        &mut quiet(),
    )
    .unwrap()
    .unwrap();
    let owned = retain(
        &mut g,
        e.prepared.shared_inputs(),
        f.architectures[1],
        1,
        &mut quiet(),
    )
    .unwrap()
    .unwrap();
    let legacy = retain(
        &mut g,
        e.prepared.shared_inputs(),
        f.architectures[0],
        1,
        &mut quiet(),
    )
    .unwrap()
    .unwrap();
    assert_ne!(f.architectures[0], f.architectures[1]);
    assert_eq!(data(&g, base.ring).source.object, 0);
    assert_eq!(data(&g, owned.ring).source.object, 1);
    assert_ne!(
        data(&g, base.ring).source.reference,
        data(&g, owned.ring).source.reference
    );
    for i in 0..2 {
        assert_eq!(coordinates(&g, base.nu[i]), coordinates(&g, owned.nu[i]));
        assert_eq!(coordinates(&g, legacy.nu[i]), coordinates(&g, owned.nu[i]));
    }
    assert_eq!(data(&g, legacy.ring).source.reference, f.architectures[0]);
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn owned_consumer_rejects_wrong_index_component_configuration_and_subject_without_appending() {
    let e = example(false, BODY);
    let mut g = graph(&e);
    let f = family(&e, &mut g, "a");
    let owned = f.architectures[1];
    let config = g.nodes[owned.0].arguments[2];
    let subject = g.nodes[owned.0].arguments[1];
    assert_eq!(
        g.nodes[config.0].ty,
        NodeType::Construction(T::Configuration)
    );
    let before = g.nodes.len();
    for (consumer, index) in [
        (owned, 0),
        (owned, 2),
        (owned, usize::MAX),
        (f.objects[1], 1),
        (f.objects[0], 0),
        (config, 1),
        (subject, 1),
    ] {
        assert!(
            retain(
                &mut g,
                e.prepared.shared_inputs(),
                consumer,
                index,
                &mut quiet()
            )
            .is_err(),
            "{consumer:?}/{index}"
        );
        assert_eq!(g.nodes.len(), before);
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn owned_missing_observation_keeps_symbolic_domain_originals_and_omits_evaluation() {
    let e = example(true, BODY);
    let mut g = graph(&e);
    let f = family(&e, &mut g, "b");
    let d = retain(
        &mut g,
        e.prepared.shared_inputs(),
        f.architectures[1],
        1,
        &mut quiet(),
    )
    .unwrap()
    .unwrap();
    assert_eq!(d.epsilon, [None, None]);
    assert!(d.evaluation.is_none());
    assert_eq!(d.originals.len(), 2);
    assert_eq!(coordinates(&g, d.nu[0]), ["1", "0"]);
    assert_eq!(coordinates(&g, d.nu[1]), ["0", "1"]);
    assert!(matches!(data(&g,d.domain).part(),Part::Domain{elements,..} if elements.len()==2));
    assert!(
        !g.nodes[d.ring.0]
            .support
            .iter()
            .any(|f| f.atom.as_deref() == Some("qx"))
    );
    assert!(
        g.nodes[d.ring.0]
            .support
            .iter()
            .any(|f| f.subject == "q" && f.field.is_none())
    );
    assert_eq!(data(&g, d.ring).source.reference, f.architectures[1]);
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn owned_law_preserves_full_parameter_columns_original_operands_and_generators() {
    let e = example(
        false,
        "law required grid(c:Part,n:Fp(2),b:Bool):let x=c.quantity in x=n;",
    );
    let mut g = graph(&e);
    let f = family(&e, &mut g, "a");
    let d = retain(
        &mut g,
        e.prepared.shared_inputs(),
        f.architectures[1],
        1,
        &mut quiet(),
    )
    .unwrap()
    .unwrap();
    assert_eq!(d.originals.len(), 4);
    assert_eq!(d.operands.len(), 4);
    assert_eq!(d.nu.len(), 4);
    let values = d.nu.iter().map(|r| coordinates(&g, *r)).collect::<Vec<_>>();
    assert_eq!(values.iter().filter(|v| **v == ["0", "1"]).count(), 2);
    assert_eq!(values.iter().filter(|v| **v == ["1", "0"]).count(), 2);
    let mut bindings = std::collections::BTreeSet::new();
    for row in &d.originals {
        assert_eq!(row.bindings.len(), 3);
        bindings.insert(
            row.bindings
                .iter()
                .map(|b| {
                    (
                        b.name.clone(),
                        g.scalar(b.value).unwrap().wire().canonical(),
                    )
                })
                .collect::<Vec<_>>(),
        );
        let Part::Source {
            location,
            parameters,
            ..
        } = data(&g, row.body).part()
        else {
            panic!("source")
        };
        assert!(parameters.is_empty());
        let Location::Law { span } = location else {
            panic!("law location")
        };
        let law = std::str::from_utf8(e.prepared.inputs().sources().law().bytes()).unwrap();
        assert_eq!(&law[span.0..span.1], "let x=c.quantity in x=n");
        assert_eq!(property(&g, row.row, "role"), Json::str("required"));
    }
    assert_eq!(bindings.len(), 4);
    assert!(
        matches!(data(&g,d.required).part(),Part::Ideal{generators,required:true,..} if generators==&d.nu)
    );
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn cached_owned_source_rejects_changed_consumer_index_origin_and_node_metadata() {
    let e = example(false, BODY);
    let mut g = graph(&e);
    let fa = family(&e, &mut g, "a");
    let fb = family(&e, &mut g, "b");
    let d = retain(
        &mut g,
        e.prepared.shared_inputs(),
        fa.architectures[1],
        1,
        &mut quiet(),
    )
    .unwrap()
    .unwrap();
    let n = g.nodes[d.ring.0].clone();
    let source = data(&g, d.ring).source.clone();
    let mut c = quiet();
    let env = Environment::new(e.prepared.inputs(), &mut c).unwrap();
    let Some(Payload::Construction(value)) = &n.payload else {
        panic!("native")
    };
    env.recheck_finite_law_diagram(&g, value).unwrap();
    env.recheck_finite_law_diagram(&g, value).unwrap();
    assert_eq!(env.verified_finite_law_diagrams.borrow().len(), 1);
    for mode in 0..8 {
        let mut changed = (*source).clone();
        match mode {
            0 => changed.reference = fb.architectures[1],
            1 => changed.reference = fa.objects[1],
            2 => changed.object = 0,
            3 => changed.object = usize::MAX,
            4 => changed.support.clear(),
            5 => changed.scope.assignments = false,
            6 => changed.parts.reverse(),
            _ => changed.outputs.nu.reverse(),
        }
        let mut value = value.clone();
        let D::FiniteLaw(data) = &mut value.data else {
            panic!("finite")
        };
        data.source = Arc::new(changed);
        assert!(
            env.recheck_finite_law_diagram(&g, &value).is_err(),
            "mode {mode}"
        );
    }
    for mode in 0..5 {
        let mut nodes = g.nodes.clone();
        let n = &mut nodes[d.ring.0];
        match mode {
            0 => n.arguments[0] = fb.architectures[1],
            1 => n.support.clear(),
            2 => n.scope.assignments = false,
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
        assert!(replay(&e, &nodes, &g.contexts).is_err(), "node {mode}");
    }
    let mut changed = replay(&e, &g.nodes, &g.contexts).unwrap();
    let root = architecture(&changed, "a");
    let Some(Payload::Construction(v)) = &mut changed.nodes[root.0].payload else {
        panic!("native")
    };
    let Some(Payload::Construction(other)) = &g.nodes[architecture(&g, "b").0].payload else {
        panic!("native")
    };
    v.witness = other.witness.clone();
    assert!(env.recheck_finite_law_diagram(&changed, value).is_err());
    let other = example(true, BODY);
    let mut c = quiet();
    let other_env = Environment::new(other.prepared.inputs(), &mut c).unwrap();
    assert!(other_env.recheck_finite_law_diagram(&g, value).is_err());
    replay(&e, &g.nodes, &g.contexts).unwrap();
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
fn signal_stops_on_owned_law_preserve_the_original_family_and_validate_finished_prefixes() {
    let e = example(false, BODY);
    let mut initial = graph(&e);
    let f = family(&e, &mut initial, "a");
    let owned = f.architectures[1];
    let before = initial.nodes.len();
    let count = std::rc::Rc::new(std::cell::Cell::new(0));
    let seen = count.clone();
    let mut c = Control::new(move |p| {
        if p == Checkpoint::FiniteLawFunction {
            seen.set(seen.get() + 1);
        }
        None
    });
    let mut g = replay(&e, &initial.nodes, &initial.contexts).unwrap();
    retain(&mut g, e.prepared.shared_inputs(), owned, 1, &mut c)
        .unwrap()
        .unwrap();
    let total = count.get();
    assert!(total > 20);
    let mut nonempty = false;
    for signal in [crate::result::Signal::Int, crate::result::Signal::Term] {
        for at in [1, 5, total - 1, total] {
            let mut g = replay(&e, &initial.nodes, &initial.contexts).unwrap();
            assert!(matches!(
                retain(
                    &mut g,
                    e.prepared.shared_inputs(),
                    owned,
                    1,
                    &mut stopping(signal, at)
                ),
                Err(ValidationFailure::Stop(_))
            ));
            assert_eq!(&g.nodes[..before], &initial.nodes[..]);
            assert_eq!(&g.contexts[..before], &initial.contexts[..]);
            nonempty |= g.nodes.len() > before;
            replay(&e, &g.nodes, &g.contexts).unwrap();
        }
    }
    assert!(nonempty);
}

#[test]
fn two_owned_consumers_share_original_domain_but_keep_their_own_applicability() {
    let map = MAP
        .replace(
            r#""id":"qo","subject":"q","field":"Finite.Part.owner","value":["v","b"]"#,
            r#""id":"qo","subject":"q","field":"Finite.Part.owner","value":["v","a"]"#,
        )
        .replace(
            r#""id":"my","subject":"m","field":"Finite.Migration.to","value":["v","b"]"#,
            r#""id":"my","subject":"m","field":"Finite.Migration.to","value":["v","a"]"#,
        )
        .replace(
            r#""value":[[["v","p"],["v","q"]]]"#,
            r#""value":[[["v","p"],["v","p"]],[["v","q"],["v","q"]]]"#,
        );
    let e = evaluate_observed_bytes(
        custom_sources(DEFINITION, &map, BODY),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &mut quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let f = family(&e, &mut g, "a");
    assert_eq!(f.architectures.len(), 3);
    let mut results = vec![];
    for (index, target) in [(1, "p"), (2, "q")] {
        let d = retain(
            &mut g,
            e.prepared.shared_inputs(),
            f.architectures[index],
            index,
            &mut quiet(),
        )
        .unwrap()
        .unwrap();
        assert_eq!(d.nu.len(), 4);
        assert_eq!(d.originals.len(), 4);
        assert!(matches!(data(&g,d.domain).part(),Part::Domain{elements,..} if elements.len()==4));
        for (position, (instance, _)) in d.components.iter().enumerate() {
            let original = &data(&g, d.ring).source.architecture.readings().instances()[*instance];
            let subject = &original.bindings()[0].subject().subject;
            let constant = usize::from(original.declaration().name == "Chosen.one");
            let applies = subject == target;
            let expected = (0..4)
                .map(|point| {
                    let value = if subject == "p" { point / 2 } else { point % 2 };
                    usize::from(applies && value != constant).to_string()
                })
                .collect::<Vec<_>>();
            assert_eq!(coordinates(&g, d.nu[position]), expected);
            let observed =
                usize::from(applies && usize::from(subject == "q") != constant).to_string();
            assert_eq!(
                coordinates(&g, d.epsilon[position].unwrap()),
                vec![observed; 4]
            );
        }
        results.push(d);
    }
    assert!(Arc::ptr_eq(
        &data(&g, results[0].ring).source.architecture,
        &data(&g, results[1].ring).source.architecture
    ));
    for index in [0, 2] {
        let before = g.nodes.len();
        assert!(
            retain(
                &mut g,
                e.prepared.shared_inputs(),
                f.architectures[1],
                index,
                &mut quiet()
            )
            .is_err()
        );
        assert_eq!(g.nodes.len(), before);
    }
    let Some(Payload::Construction(value)) = &g.nodes[results[0].ring.0].payload else {
        panic!("native")
    };
    let mut forged = (**value).clone();
    let D::FiniteLaw(v) = &mut forged.data else {
        panic!("finite")
    };
    let mut changed = (*v.source).clone();
    changed.reference = f.architectures[2];
    v.source = Arc::new(changed);
    assert!(
        Environment::new(e.prepared.inputs(), &mut quiet())
            .unwrap()
            .recheck_finite_law_diagram(&g, &forged)
            .is_err()
    );
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn cache_hit_still_checks_the_actual_owned_architecture_node_and_root_request() {
    let e = example(false, BODY);
    let mut g = graph(&e);
    let f = family(&e, &mut g, "a");
    let owned = f.architectures[1];
    let d = retain(&mut g, e.prepared.shared_inputs(), owned, 1, &mut quiet())
        .unwrap()
        .unwrap();
    let Some(Payload::Construction(value)) = &g.nodes[d.ring.0].payload else {
        panic!("native")
    };
    let mut c = quiet();
    let env = Environment::new(e.prepared.inputs(), &mut c).unwrap();
    env.recheck_finite_law_diagram(&g, value).unwrap();
    for mode in 0..5 {
        let mut changed = replay(&e, &g.nodes, &g.contexts).unwrap();
        match mode {
            0 => changed.nodes[owned.0].support.clear(),
            1 => changed.nodes[owned.0].scope.assignments = true,
            2 => changed.nodes[owned.0].arguments.reverse(),
            3 => changed.nodes[owned.0].ty = NodeType::Construction(T::ObjectComponent),
            _ => changed.requests[0].text = "changed consumer".into(),
        }
        assert!(
            env.recheck_finite_law_diagram(&changed, value).is_err(),
            "cache mode {mode}"
        );
    }
    assert_eq!(env.verified_finite_law_diagrams.borrow().len(), 1);
}

#[test]
fn actual_owned_consumers_preserve_reading_identity_and_reject_foreign_cached_witnesses() {
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
    let mut results = vec![];
    for name in ["Chosen", "Other"] {
        let root=NodeRef(g.nodes.iter().position(|n|matches!(&n.payload,Some(Payload::Construction(v)) if matches!((&v.witness,&v.data),(Witness::Architecture(a),D::Architecture{..}) if a.construction().root().subject=="a"&&a.construction().reading()==name))).unwrap());
        g.active = g.context_at(root.0);
        let f = objects::retain(&mut g, e.prepared.shared_inputs(), root, &mut quiet())
            .unwrap()
            .unwrap();
        let d = retain(
            &mut g,
            e.prepared.shared_inputs(),
            f.architectures[1],
            1,
            &mut quiet(),
        )
        .unwrap()
        .unwrap();
        assert!(g.nodes[d.ring.0].scope.readings.contains(name));
        assert_eq!(
            data(&g, d.ring)
                .source
                .architecture
                .construction()
                .reading(),
            name
        );
        results.push(d);
    }
    let first = &results[0];
    g.active = g.context_at(first.ring.0);
    let Some(Payload::Construction(value)) = &g.nodes[first.ring.0].payload else {
        panic!("native")
    };
    let mut c = quiet();
    let env = Environment::new(e.prepared.inputs(), &mut c).unwrap();
    env.recheck_finite_law_diagram(&g, value).unwrap();
    let mut foreign = (**value).clone();
    foreign.witness = Witness::Architecture(data(&g, results[1].ring).source.architecture.clone());
    assert!(env.recheck_finite_law_diagram(&g, &foreign).is_err());
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
