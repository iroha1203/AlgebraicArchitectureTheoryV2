use super::*;
use crate::{input::InputSources, observed::evaluate_observed_bytes};

use crate::control::quiet;
const DEFINITION: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Finite","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Finite.Root","meaning":"有限入力の対象。","parameters":[],"fields":[],"alignments":[]},{"kind":"entity","name":"Finite.Part","meaning":"有限入力の対象。","parameters":[{"name":"owner","type":["Ref","Finite.Root"],"meaning":"元の型付き値。"}],"fields":[{"name":"quantity","type":"Z","meaning":"元の型付き値。"}],"alignments":[]},{"kind":"correspondence","name":"Finite.Migration","meaning":"有限入力の対象。","parameters":[{"name":"from","type":["Ref","Finite.Root"],"meaning":"元の型付き値。"},{"name":"to","type":["Ref","Finite.Root"],"meaning":"元の型付き値。"}],"fields":[{"name":"states","type":["Map",["Owned","Finite.Part","from"],["Owned","Finite.Part","to"]],"meaning":"元の型付き値。"}],"alignments":[]}]}]}"#;
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
    let D::PolynomialLaw(data) = &v.data else {
        panic!("finite")
    };
    data
}
fn wire(g: &Graph, r: NodeRef) -> Json {
    data(g, r).wire()
}
fn terms(g: &Graph, r: NodeRef) -> Vec<(Json, Vec<usize>)> {
    let Part::Polynomial { terms, .. } = data(g, r).part() else {
        panic!("polynomial")
    };
    terms
        .iter()
        .map(|(c, p)| (g.scalar(*c).unwrap().wire(), p.clone()))
        .collect()
}
#[test]
fn z_polynomial_diagram_keeps_shared_symbols_raw_epsilon_ideals_and_evaluation_images() {
    let e = example(false, BODY);
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet()).unwrap();
    assert_eq!(d.rings.len(), 1);
    assert_eq!(d.coordinates.len(), 2);
    assert_eq!(d.status, EquationPresentationStatus::Ready);
    assert_eq!(
        wire(&g, d.bases[0]),
        Json::obj([("kind", Json::str("scalar")), ("scalar", Json::str("Z"))])
    );
    let Part::Ring { variables, .. } = data(&g, d.rings[0]).part() else {
        panic!("ring")
    };
    assert_eq!(variables.len(), 1);
    assert_eq!(variables[0].field.subject, "p");
    assert_eq!(
        variables[0].field.field.as_deref(),
        Some("Finite.Part.quantity")
    );
    assert_eq!(variables[0].component, []);
    let source = &data(&g, d.rings[0]).source;
    assert_eq!(source.core.as_ref().unwrap().rings().len(), 1);
    for q in &d.coordinates {
        let original = &source.core.as_ref().unwrap().occurrences()[q.occurrence];
        let declaration = &source.architecture.readings().instances()[original.position.instance]
            .declaration()
            .name;
        assert_eq!(q.ring, Some(d.rings[0]));
        assert_eq!(q.guard, EquationGuard::AlwaysTrue);
        let expected = if declaration == "Chosen.one" {
            vec![(Json::str("-1"), vec![0]), (Json::str("1"), vec![1])]
        } else {
            vec![(Json::str("1"), vec![1])]
        };
        assert_eq!(terms(&g, q.nu.unwrap()), expected);
        assert_eq!(terms(&g, q.left.unwrap()), vec![(Json::str("1"), vec![1])]);
        if declaration == "Chosen.zero" {
            assert!(terms(&g, q.epsilon.unwrap()).is_empty());
        } else {
            assert_eq!(
                terms(&g, q.epsilon.unwrap()),
                vec![(Json::str("-1"), vec![0])]
            );
        }
        assert_eq!(
            terms(&g, q.epsilon.unwrap()),
            terms(&g, q.residual.unwrap())
        );
        assert!(
            matches!(data(&g,q.witness.unwrap()).part(),Part::Ideal{generators,required:false,..} if generators==&vec![q.nu.unwrap()])
        );
    }
    let Part::Ideal {
        generators,
        required,
        ..
    } = data(&g, d.required[0]).part()
    else {
        panic!("ideal")
    };
    assert!(*required);
    assert_eq!(generators.len(), 1);
    let Part::Evaluation {
        source,
        target,
        images,
    } = data(&g, d.evaluations[0].unwrap()).part()
    else {
        panic!("evaluation")
    };
    assert_eq!((*source, *target), (d.rings[0], d.bases[0]));
    assert_eq!(images.len(), 1);
    assert!(terms(&g, images[0]).is_empty());
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn missing_symbol_keeps_polynomials_but_never_fabricates_epsilon_or_total_evaluation() {
    let e = example(true, BODY);
    let mut g = graph(&e);
    let b = architecture(&g, "b");
    let d = retain(&mut g, e.prepared.shared_inputs(), b, 0, &mut quiet()).unwrap();
    assert_eq!(d.rings.len(), 1);
    assert!(d.evaluations[0].is_none());
    assert_eq!(d.status, EquationPresentationStatus::Undetermined);
    assert!(
        d.coordinates
            .iter()
            .all(|q| q.nu.is_some() && q.epsilon.is_none() && q.residual.is_none())
    );
    assert!(
        !g.nodes[d.rings[0].0]
            .support
            .iter()
            .any(|f| f.atom.as_deref() == Some("qx"))
    );
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn q_and_fp_keep_their_original_coefficient_rings_and_exact_constant_encoding() {
    for (ty, zero, one, coefficient) in [
        (
            "Q",
            r#"["0","1"]"#,
            r#"["1","1"]"#,
            Json::Arr(vec![Json::str("1"), Json::str("1")]),
        ),
        ("Fp", r#""0""#, r#""1""#, Json::str("1")),
    ] {
        let definition = DEFINITION.replace(
            r#""type":"Z""#,
            if ty == "Q" {
                r#""type":"Q""#
            } else {
                r#""type":["Fp","2"]"#
            },
        );
        let map = MAP
            .replace(r#""value":"0""#, &format!("\"value\":{zero}"))
            .replace(r#""value":"1""#, &format!("\"value\":{one}"));
        let e=evaluate_observed_bytes(custom_sources(&definition,&map,"law required twice(c:Part):c.quantity+c.quantity=0;law optional one(c:Part):c.quantity=1;"),&["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],&mut quiet()).unwrap();
        let mut g = graph(&e);
        let a = architecture(&g, "a");
        let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet()).unwrap();
        assert_eq!(d.rings.len(), 1);
        assert_eq!(d.domains.len(), 1);
        let domain_type = if ty == "Q" {
            Type::Q
        } else {
            Type::Fp("2".into())
        };
        assert_eq!(
            wire(&g, d.domains[0]),
            Json::obj([("kind", Json::str("type")), ("type", domain_type.wire())])
        );
        let source = &data(&g, d.rings[0]).source;
        for q in &d.coordinates {
            let original = &source.core.as_ref().unwrap().occurrences()[q.occurrence];
            let name = &source.architecture.readings().instances()[original.position.instance]
                .declaration()
                .name;
            if name == "Chosen.twice" {
                if ty == "Fp" {
                    assert!(terms(&g, q.nu.unwrap()).is_empty());
                } else {
                    assert_eq!(
                        terms(&g, q.nu.unwrap()),
                        vec![(Json::Arr(vec![Json::str("2"), Json::str("1")]), vec![1])]
                    );
                }
            } else {
                assert_eq!(
                    terms(&g, q.left.unwrap()),
                    vec![(coefficient.clone(), vec![1])]
                );
            }
        }
        replay(&e, &g.nodes, &g.contexts).unwrap();
    }
}

fn two_owned_example(body: &str) -> ObservedEvaluation {
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
    evaluate_observed_bytes(
        custom_sources(DEFINITION, &map, body),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &mut quiet(),
    )
    .unwrap()
}
#[test]
fn dense_powers_sort_by_powers_and_keep_all_shared_positions_and_aggregated_coefficients() {
    let e = two_owned_example("law required addition(c:Part,d:Part):c.quantity+d.quantity=0;");
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet()).unwrap();
    assert_eq!(d.rings.len(), 1);
    assert_eq!(d.coordinates.len(), 4);
    let Part::Ring { variables, .. } = data(&g, d.rings[0]).part() else {
        panic!("ring")
    };
    assert_eq!(
        variables
            .iter()
            .map(|v| v.field.subject.as_str())
            .collect::<Vec<_>>(),
        ["p", "q"]
    );
    let mut mixed = 0;
    let mut doubled = 0;
    for q in &d.coordinates {
        let ts = terms(&g, q.nu.unwrap());
        assert!(ts.iter().all(|(_, p)| p.len() == 2));
        if ts.len() == 2 {
            mixed += 1;
            assert_eq!(
                ts,
                vec![(Json::str("1"), vec![0, 1]), (Json::str("1"), vec![1, 0])]
            );
        } else {
            doubled += 1;
            assert_eq!(ts[0].0, Json::str("2"));
            assert!(ts[0].1 == [1, 0] || ts[0].1 == [0, 1]);
        }
    }
    assert_eq!((mixed, doubled), (2, 2));
    assert!(
        matches!(data(&g,d.required[0]).part(),Part::Ideal{generators,..} if generators.len()==4)
    );
    let Part::Evaluation { images, .. } = data(&g, d.evaluations[0].unwrap()).part() else {
        panic!("evaluation")
    };
    assert!(terms(&g, images[0]).is_empty());
    assert_eq!(terms(&g, images[1]), vec![(Json::str("1"), vec![])]);
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn tuple_components_keep_separate_z_q_rings_and_original_component_positions() {
    let definition = DEFINITION.replace(r#""type":"Z""#, r#""type":["Tuple","Z","Q"]"#);
    let map = MAP
        .replace(r#""value":"0""#, r#""value":["0",["0","1"]]"#)
        .replace(r#""value":"1""#, r#""value":["1",["1","1"]]"#);
    let e = evaluate_observed_bytes(
        custom_sources(
            &definition,
            &map,
            "law required pair(c:Part):c.quantity=(0,0);",
        ),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &mut quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet()).unwrap();
    assert_eq!(d.rings.len(), 2);
    assert_eq!(d.coordinates.len(), 2);
    for (q, expected) in d.coordinates.iter().zip([Type::Z, Type::Q]) {
        assert_eq!(q.ty, expected);
        let index = usize::from(expected == Type::Q);
        assert_eq!(q.component, [index]);
        let Part::Ring { variables, .. } = data(&g, d.rings[index]).part() else {
            panic!("ring")
        };
        assert_eq!(variables.len(), 1);
        assert_eq!(variables[0].component, [index]);
        assert_eq!(variables[0].ty, expected);
        assert!(terms(&g, q.epsilon.unwrap()).is_empty());
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn false_and_state_dependent_guards_keep_nonzero_raw_epsilon_separate_from_zero_residual() {
    let e = example(
        false,
        "law required off(c:Part) when false:c.quantity=1;law required dynamic(c:Part) when c.quantity>0:c.quantity=1;law required on(c:Part) when true:c.quantity=0;",
    );
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet()).unwrap();
    assert_eq!(d.status, EquationPresentationStatus::UnsupportedAlgorithm);
    for q in &d.coordinates {
        match q.guard {
            EquationGuard::AlwaysFalse | EquationGuard::StateDependent => {
                assert_eq!(
                    terms(&g, q.epsilon.unwrap()),
                    vec![(Json::str("-1"), vec![0])]
                );
                assert!(terms(&g, q.residual.unwrap()).is_empty());
                assert_ne!(q.epsilon, q.residual);
            }
            EquationGuard::AlwaysTrue => assert!(terms(&g, q.epsilon.unwrap()).is_empty()),
            _ => panic!("guard"),
        }
    }
    assert!(
        matches!(data(&g,d.required[0]).part(),Part::Ideal{generators,..} if generators.len()==1)
    );
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn owned_architecture_keeps_containing_root_and_outside_object_residual_without_raw_value() {
    let e = two_owned_example("law required zero(c:Part):c.quantity=0;");
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let objects = crate::observed::object_component_diagram::retain(
        &mut g,
        e.prepared.shared_inputs(),
        a,
        &mut quiet(),
    )
    .unwrap()
    .unwrap();
    assert_eq!(objects.architectures.len(), 3);
    for index in [1, 2] {
        let d = retain(
            &mut g,
            e.prepared.shared_inputs(),
            objects.architectures[index],
            index,
            &mut quiet(),
        )
        .unwrap();
        assert_eq!(d.coordinates.len(), 2);
        for q in &d.coordinates {
            let source = &data(&g, q.ring.unwrap()).source;
            assert_eq!(source.architecture.construction().root().subject, "a");
            assert_eq!(source.reference, objects.architectures[index]);
            assert_eq!(source.object, index);
            if q.guard == EquationGuard::OutsideObject {
                let nu = q.nu.unwrap();
                assert!(terms(&g, nu).iter().any(|(_, powers)| powers.iter().any(|p| *p == 1)));
                assert!(q.epsilon.is_none());
                assert!(terms(&g, q.residual.unwrap()).is_empty());
                let Part::Ideal { generators, .. } = data(&g, q.witness.unwrap()).part() else { panic!("ideal") };
                assert_eq!(generators, &vec![nu]);
            } else {
                assert_eq!(q.guard, EquationGuard::AlwaysTrue);
                let expected = if index == 1 {
                    vec![]
                } else {
                    vec![(Json::str("1"), vec![0, 0])]
                };
                assert_eq!(terms(&g, q.epsilon.unwrap()), expected);
            }
        }
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn zero_cancellation_keeps_the_original_symbol_support_and_zero_polynomial_encoding() {
    let e = example(
        false,
        "law required zero(c:Part):let x=c.quantity in x+x-2*x=0;",
    );
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet()).unwrap();
    assert_eq!(d.coordinates.len(), 1);
    assert!(terms(&g, d.coordinates[0].nu.unwrap()).is_empty());
    let Part::Ring { variables, .. } = data(&g, d.rings[0]).part() else {
        panic!("ring")
    };
    assert_eq!(variables.len(), 1);
    assert!(
        g.nodes[d.rings[0].0]
            .support
            .iter()
            .any(|f| f.atom.as_deref() == Some("px"))
    );
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn recheck_rejects_changed_coefficients_powers_symbols_ideals_maps_and_coordinate_metadata() {
    let e = example(false, BODY);
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet()).unwrap();
    let source = data(&g, d.rings[0]).source.clone();
    let poly = d.coordinates[0].nu.unwrap().0 - source.base;
    let Part::Polynomial { terms, .. } = &source.parts[poly] else {
        panic!("nu polynomial")
    };
    let scalar = terms[0].0.0 - source.base;
    assert!(matches!(&source.parts[scalar], Part::Scalar(Scalar::Z(_))));
    for mode in 0..13 {
        let mut changed = (*source).clone();
        match mode {
            0 => changed.parts[d.bases[0].0 - source.base] = Part::Base(Type::Q),
            1 => {
                if let Part::Ring { variables, .. } = &mut changed.parts[d.rings[0].0 - source.base]
                {
                    variables[0].field.subject = "q".into();
                }
            }
            2 => {
                if let Part::Ring { variables, .. } = &mut changed.parts[d.rings[0].0 - source.base]
                {
                    variables[0].component.push(1);
                }
            }
            3 => {
                if let Part::Ring { variables, .. } = &mut changed.parts[d.rings[0].0 - source.base]
                {
                    variables[0].ty = Type::Q;
                }
            }
            4 => {
                if let Part::Polynomial { terms, .. } = &mut changed.parts[poly] {
                    terms[0].1.push(0);
                }
            }
            5 => changed.parts[scalar] = Part::Scalar(Scalar::Z(3.into())),
            6 => {
                if let Part::Ideal { generators, .. } =
                    &mut changed.parts[d.required[0].0 - source.base]
                {
                    generators.clear();
                }
            }
            7 => {
                if let Part::Evaluation { images, .. } =
                    &mut changed.parts[d.evaluations[0].unwrap().0 - source.base]
                {
                    images.clear();
                }
            }
            8 => changed.outputs.coordinates[0].ty = Type::Q,
            9 => changed.outputs.coordinates[0].component.push(1),
            10 => changed.outputs.coordinates[0].guard = EquationGuard::AlwaysFalse,
            11 => changed.support.clear(),
            _ => changed.scope.assignments = false,
        }
        assert!(
            changed
                .recheck(e.prepared.inputs(), &source.architecture, &mut quiet())
                .is_err(),
            "mode {mode}"
        );
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn cached_native_validation_rejects_foreign_consumer_input_witness_request_and_nodes() {
    let e = example(false, BODY);
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let b = architecture(&g, "b");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet()).unwrap();
    let source = data(&g, d.rings[0]).source.clone();
    let n = &g.nodes[d.rings[0].0];
    let Some(Payload::Construction(value)) = &n.payload else {
        panic!("native")
    };
    let mut c = quiet();
    let env = Environment::new(e.prepared.inputs(), &mut c).unwrap();
    env.recheck_polynomial_law_diagram(&g, value).unwrap();
    env.recheck_polynomial_law_diagram(&g, value).unwrap();
    assert_eq!(env.results.verified::<std::sync::Arc<crate::observed::polynomial_law_diagram::Source>>().len(), 1);
    for mode in 0..4 {
        let mut forged = (**value).clone();
        let D::PolynomialLaw(data) = &mut forged.data else {
            panic!("poly")
        };
        let mut altered = (*source).clone();
        match mode {
            0 => altered.reference = b,
            1 => altered.object = 1,
            2 => altered.base += 1,
            _ => altered.inputs = example(true, BODY).prepared.shared_inputs(),
        };
        data.source = Arc::new(altered);
        assert!(
            env.recheck_polynomial_law_diagram(&g, &forged).is_err(),
            "consumer {mode}"
        );
    }
    let Some(Payload::Construction(other)) = &g.nodes[b.0].payload else {
        panic!("architecture")
    };
    let mut forged = (**value).clone();
    forged.witness = other.witness.clone();
    assert!(env.recheck_polynomial_law_diagram(&g, &forged).is_err());
    let mut changed = replay(&e, &g.nodes, &g.contexts).unwrap();
    changed.requests[0].text = "different request".into();
    assert!(env.recheck_polynomial_law_diagram(&changed, value).is_err());
    for mode in 0..6 {
        let mut nodes = g.nodes.clone();
        let n = &mut nodes[d.rings[0].0];
        match mode {
            0 => n.arguments.clear(),
            1 => n.arguments[0] = b,
            2 => n.ty = NodeType::Construction(T::Ideal),
            3 => n.support.clear(),
            4 => n.scope.assignments = false,
            _ => {
                let Some(Payload::Construction(v)) = &mut n.payload else {
                    panic!("native")
                };
                let D::PolynomialLaw(d) = &mut v.data else {
                    panic!("poly")
                };
                d.index = usize::MAX;
            }
        }
        assert!(replay(&e, &nodes, &g.contexts).is_err(), "node {mode}");
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
fn stopping(signal: crate::result::Signal, at: usize) -> Control {
    let seen = std::rc::Rc::new(std::cell::Cell::new(0));
    Control::new(move |p| {
        if p == Checkpoint::EquationPresentation {
            seen.set(seen.get() + 1);
        }
        (seen.get() >= at).then_some(signal)
    })
}
#[test]
fn signal_stops_propagate_through_the_kernel_and_keep_only_complete_native_prefixes() {
    let e = example(false, BODY);
    let mut complete = graph(&e);
    let a = architecture(&complete, "a");
    let before = complete.nodes.len();
    let seen = std::rc::Rc::new(std::cell::Cell::new(0));
    let count = seen.clone();
    let mut c = Control::new(move |p| {
        if p == Checkpoint::EquationPresentation {
            count.set(count.get() + 1);
        }
        None
    });
    retain(&mut complete, e.prepared.shared_inputs(), a, 0, &mut c).unwrap();
    let total = seen.get();
    assert!(total > 20);
    let mut nonempty = false;
    for signal in [crate::result::Signal::Int, crate::result::Signal::Term] {
        for at in [1, 5, total / 2, total - 1, total] {
            let mut g = graph(&e);
            assert!(
                matches!(
                    retain(
                        &mut g,
                        e.prepared.shared_inputs(),
                        a,
                        0,
                        &mut stopping(signal, at)
                    ),
                    Err(ValidationFailure::Stop(_))
                ),
                "{signal:?}/{at}"
            );
            assert_eq!(&g.nodes[..before], &e.nodes[..]);
            assert_eq!(&g.contexts[..before], &e.contexts[..]);
            nonempty |= g.nodes.len() > before;
            replay(&e, &g.nodes, &g.contexts).unwrap();
        }
    }
    assert!(nonempty);
    replay(&e, &complete.nodes, &complete.contexts).unwrap();
}
#[test]
fn identical_polynomial_values_from_different_readings_keep_separate_origins_and_cache_entries() {
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
        let d = retain(&mut g, e.prepared.shared_inputs(), root, 0, &mut quiet()).unwrap();
        assert!(g.nodes[d.rings[0].0].scope.readings.contains(name));
        assert_eq!(
            data(&g, d.rings[0])
                .source
                .architecture
                .construction()
                .reading(),
            name
        );
        results.push(d);
    }
    let mut c = quiet();
    let env = Environment::new(e.prepared.inputs(), &mut c).unwrap();
    for d in &results {
        let Some(Payload::Construction(v)) = &g.nodes[d.rings[0].0].payload else {
            panic!("native")
        };
        env.recheck_polynomial_law_diagram(&g, v).unwrap();
    }
    assert_eq!(env.results.verified::<std::sync::Arc<crate::observed::polynomial_law_diagram::Source>>().len(), 2);
    let Some(Payload::Construction(v)) = &g.nodes[results[0].rings[0].0].payload else {
        panic!("native")
    };
    let mut forged = (**v).clone();
    forged.witness =
        Witness::Architecture(data(&g, results[1].rings[0]).source.architecture.clone());
    assert!(env.recheck_polynomial_law_diagram(&g, &forged).is_err());
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn empty_families_and_nonnumeric_polynomial_status_do_not_fabricate_zero_coordinates() {
    for body in ["", "law required plain(c:Part):true;"] {
        let e = example(false, body);
        let mut g = graph(&e);
        let a = architecture(&g, "a");
        let before = g.nodes.len();
        let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet()).unwrap();
        assert!(d.rings.is_empty());
        assert!(d.domains.is_empty());
        assert!(d.evaluations.is_empty());
        assert!(d.required.is_empty());
        if body.is_empty() {
            assert_eq!(g.nodes.len(), before + 1);
            assert_eq!(d.context, Some(NodeRef(before)));
            let Part::Equation(crate::observed::equation_presentation_node::Part::Context {
                base,
                carrier,
                dependencies,
                laws,
                ..
            }) = data(&g, NodeRef(before)).part()
            else {
                panic!("global Context only");
            };
            assert_eq!(*base, a);
            assert_eq!(carrier.len(), 12);
            assert!(dependencies.is_empty() && laws.is_empty());
            assert!(d.presentations.is_empty());
            assert!(d.originals.is_empty());
            assert!(d.coordinates.is_empty());
            assert_eq!(d.status, EquationPresentationStatus::Ready);
        } else {
            assert_eq!(d.status, EquationPresentationStatus::UnsupportedAlgorithm);
            assert!(d.presentations.is_empty());
            assert!(d.context.is_some());
            assert_eq!(d.coordinates.len(), 1);
            let q = &d.coordinates[0];
            assert_eq!(q.ty, Type::Bool);
            assert!(q.nu.is_none() && q.epsilon.is_none() && q.residual.is_none());
            assert!(q.required);
            assert!(!d.originals.is_empty());
            assert_eq!(d.readings.len(), 1);
            assert_eq!(
                g.scalar(d.readings[0].body.unwrap()).unwrap(),
                &Scalar::Bool(true)
            );
            assert_eq!(
                g.scalar(d.readings[0].holds.unwrap()).unwrap(),
                &Scalar::Bool(true)
            );
            for node in &g.nodes[before..] {
                let Some(Payload::Construction(value)) = &node.payload else {
                    panic!("original source")
                };
                let D::PolynomialLaw(data) = &value.data else {
                    panic!("polynomial source")
                };
                assert!(matches!(
                    data.part(),
                    Part::Source { .. }
                        | Part::LawInstance { .. }
                        | Part::Transform {
                            operation: Transform::Equal,
                            ..
                        }
                        | Part::Scalar(Scalar::Unit | Scalar::Subject { .. })
                        | Part::ObservedBoolean {
                            value: Scalar::Bool(true),
                            ..
                        }
                        | Part::Equation(
                            crate::observed::equation_presentation_node::Part::Context { .. }
                        )
                ));
            }
        }
        replay(&e, &g.nodes, &g.contexts).unwrap();
    }
}

#[test]
fn wrong_object_indices_and_nonarchitecture_consumers_fail_before_appending_native_values() {
    let e = example(false, BODY);
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let objects = crate::observed::object_component_diagram::retain(
        &mut g,
        e.prepared.shared_inputs(),
        a,
        &mut quiet(),
    )
    .unwrap()
    .unwrap();
    let subject = g.nodes[a.0].arguments[0];
    let configuration = g.nodes[a.0].arguments[1];
    let before = g.nodes.len();
    for (reference, index) in [
        (a, usize::MAX),
        (objects.architectures[1], 0),
        (objects.architectures[1], usize::MAX),
        (objects.objects[1], 1),
        (subject, 0),
        (configuration, 0),
        (NodeRef(usize::MAX), 0),
    ] {
        let failure = retain(
            &mut g,
            e.prepared.shared_inputs(),
            reference,
            index,
            &mut quiet(),
        )
        .unwrap_err();
        assert!(
            matches!(failure,ValidationFailure::Internal(ref message) if !message.is_empty()&&message.len()<300)
        );
        assert_eq!(g.nodes.len(), before);
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

mod sources;

#[test]
fn assignment_domains_keep_all_variable_types_and_zero_variable_unit_without_observation_enumeration()
 {
    for (body, expected, subjects, two_owned) in [
        (
            "law required constant(c:Part):0=0;",
            Type::Unit,
            vec![],
            false,
        ),
        (
            "law required single(c:Part):c.quantity=0;",
            Type::Z,
            vec!["p"],
            false,
        ),
        (
            "law required pair(x:Part,y:Part):x.quantity+y.quantity=0;",
            Type::Tuple(vec![Type::Z, Type::Z]),
            vec!["p", "q"],
            true,
        ),
    ] {
        let e = if two_owned {
            two_owned_example(body)
        } else {
            example(false, body)
        };
        let mut g = graph(&e);
        let a = architecture(&g, "a");
        let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet()).unwrap();
        assert_eq!(d.rings.len(), 1);
        assert_eq!(d.domains.len(), 1);
        let domain = d.domains[0];
        assert_eq!(g.nodes[domain.0].ty, NodeType::Domain);
        assert_eq!(g.nodes[domain.0].rule, Rule::Construction("domain"));
        assert_eq!(
            wire(&g, domain),
            Json::obj([("kind", Json::str("type")), ("type", expected.wire())])
        );
        let Part::Domain { ring, ty } = data(&g, domain).part() else {
            panic!("domain")
        };
        assert_eq!((*ring, ty), (d.rings[0], &expected));
        assert_eq!(g.nodes[domain.0].arguments, vec![a, d.rings[0]]);
        let Part::Ring { variables, .. } = data(&g, *ring).part() else {
            panic!("ring")
        };
        assert_eq!(
            variables
                .iter()
                .map(|v| v.field.subject.as_str())
                .collect::<Vec<_>>(),
            subjects
        );
        assert!(
            variables
                .iter()
                .all(|v| v.ty == Type::Z && v.component.is_empty())
        );
        assert_eq!(g.nodes[domain.0].support, g.nodes[ring.0].support);
        assert_eq!(g.nodes[domain.0].scope, g.nodes[ring.0].scope);
        replay(&e, &g.nodes, &g.contexts).unwrap();
    }
}
#[test]
fn missing_observation_keeps_full_assignment_type_without_total_evaluation() {
    let e = example(true, BODY);
    let mut g = graph(&e);
    let b = architecture(&g, "b");
    let d = retain(&mut g, e.prepared.shared_inputs(), b, 0, &mut quiet()).unwrap();
    assert_eq!(d.status, EquationPresentationStatus::Undetermined);
    assert_eq!(d.domains.len(), 1);
    assert_eq!(
        wire(&g, d.domains[0]),
        Json::obj([("kind", Json::str("type")), ("type", Json::str("Z"))])
    );
    assert!(d.evaluations[0].is_none());
    assert!(d.coordinates.iter().all(|q| q.epsilon.is_none()));
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn assignment_domain_type_ring_reference_and_output_alignment_changes_are_rejected() {
    let definition = DEFINITION.replace(r#""type":"Z""#, r#""type":["Tuple","Z","Q"]"#);
    let map = MAP
        .replace(r#""value":"0""#, r#""value":["0",["0","1"]]"#)
        .replace(r#""value":"1""#, r#""value":["1",["1","1"]]"#);
    let e = evaluate_observed_bytes(
        custom_sources(
            &definition,
            &map,
            "law required split(c:Part):c.quantity=(0,0);",
        ),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &mut quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet()).unwrap();
    assert_eq!((d.domains.len(), d.rings.len()), (2, 2));
    let source = data(&g, d.domains[0]).source.clone();
    for ((domain, ring), ty) in d.domains.iter().zip(&d.rings).zip([Type::Z, Type::Q]) {
        assert_eq!(
            wire(&g, *domain),
            Json::obj([("kind", Json::str("type")), ("type", ty.wire())])
        );
        assert!(matches!(data(&g,*domain).part(), Part::Domain{ring: r,..} if r==ring));
    }
    let index = data(&g, d.domains[0]).index;
    for mode in 0..6 {
        let mut changed = (*source).clone();
        match mode {
            0 => {
                if let Part::Domain { ty, .. } = &mut changed.parts[index] {
                    *ty = Type::Unit;
                }
            }
            1 => {
                if let Part::Domain { ring, .. } = &mut changed.parts[index] {
                    *ring = d.rings[1];
                }
            }
            2 => changed.outputs.domains.swap(0, 1),
            3 => changed.outputs.domains.clear(),
            4 => changed.outputs.domains[0] = d.rings[0],
            _ => {
                if let Part::Domain { ring, .. } = &mut changed.parts[index] {
                    *ring = d.domains[0];
                }
            }
        }
        assert!(
            changed
                .recheck(e.prepared.inputs(), &source.architecture, &mut quiet())
                .is_err(),
            "mode {mode}"
        );
    }
    for mode in 0..3 {
        let mut nodes = g.nodes.clone();
        let n = &mut nodes[d.domains[0].0];
        match mode {
            0 => n.arguments[1] = d.rings[1],
            1 => n.ty = NodeType::Value(Type::Z),
            _ => n.rule = Rule::Construction("ring"),
        }
        assert!(replay(&e, &nodes, &g.contexts).is_err(), "native {mode}");
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn polynomial_presentations_preserve_shared_ring_raw_epsilon_and_original_component_expressions() {
    use crate::observed::equation_presentation_node::Part as E;
    let e = example(
        false,
        "law required pair(c:Part):(c.quantity,c.quantity)=(0,1);",
    );
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet()).unwrap();
    assert_eq!(d.presentations.len(), 1);
    let r = d.presentations[0].unwrap();
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
    }) = data(&g, r).part()
    else {
        panic!("presentation");
    };
    assert_eq!(
        (*domain, *ring, *required, *evaluation, *context),
        (
            d.domains[0],
            d.rings[0],
            d.required[0],
            d.evaluations[0],
            d.context.unwrap()
        )
    );
    let original = d.originals.iter().find(|o| o.row == Some(0)).unwrap();
    assert_eq!(instances, &vec![original.reference]);
    assert!(original.bindings.iter().any(|b| b.name == "c"
        && matches!(g.scalar(b.value).unwrap(),Scalar::Subject{subject,..} if subject=="p")));
    assert_eq!(coordinates.len(), 2);
    assert_eq!(
        coordinates
            .iter()
            .map(|q| q.component.clone())
            .collect::<Vec<_>>(),
        [vec![0], vec![1]]
    );
    for (i, q) in coordinates.iter().enumerate() {
        let original = &d.coordinates[i];
        assert_eq!(
            (q.instance, q.lhs, q.rhs, q.nu, q.epsilon),
            (
                original.instance,
                original.lhs,
                original.rhs,
                original.nu.unwrap(),
                original.epsilon
            )
        );
        assert_eq!(witnesses[i], original.witness.unwrap());
    }
    let Part::Equation(E::Context {
        base,
        carrier,
        laws,
        ..
    }) = data(&g, d.context.unwrap()).part()
    else {
        panic!("context");
    };
    assert_eq!(*base, a);
    assert_eq!(carrier.len(), 12);
    assert_eq!(laws, &vec![original.reference]);
    assert_ne!(coordinates[0].lhs, coordinates[0].rhs);
    assert_eq!(terms(&g, coordinates[0].epsilon.unwrap()), vec![]);
    assert_eq!(
        terms(&g, coordinates[1].epsilon.unwrap()),
        vec![(Json::str("-1"), vec![0])]
    );
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn missing_polynomial_values_keep_formal_presentation_without_fabricating_epsilon_or_evaluation() {
    use crate::observed::equation_presentation_node::Part as E;
    let e = example(true, BODY);
    let mut g = graph(&e);
    let b = architecture(&g, "b");
    let d = retain(&mut g, e.prepared.shared_inputs(), b, 0, &mut quiet()).unwrap();
    let r = d.presentations[0].unwrap();
    let Part::Equation(E::Presentation {
        coordinates,
        evaluation,
        ..
    }) = data(&g, r).part()
    else {
        panic!("presentation");
    };
    assert!(evaluation.is_none());
    assert_eq!(coordinates.len(), 2);
    assert!(coordinates.iter().all(|q| q.epsilon.is_none()));
    for q in coordinates {
        assert!(matches!(data(&g, q.nu).part(), Part::Polynomial { .. }));
    }
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
        .filter(|o| o.row == Some(0))
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
    for mutation in 0..3 {
        let mut nodes = g.nodes.clone();
        match mutation {
            0 => nodes[r.0].reasons.clear(),
            1 => nodes[r.0].reasons[0].missing[0].field = Some("Finite.Part.owner".into()),
            _ => nodes[r.0].reasons[0].dependencies = vec![b],
        }
        assert!(
            replay(&e, &nodes, &g.contexts).is_err(),
            "omission reason mutation {mutation}"
        );
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn context_keeps_general_condition_and_discarded_reference_reads_outside_numeric_symbols() {
    use crate::observed::equation_presentation_node::Part as E;
    for (body, expected) in [
        (
            "law required positive(c:Part):c.quantity>0;",
            vec!["Finite.Part.quantity"],
        ),
        (
            "law required used(c:Part):let discarded=c.owner in c.quantity=0;",
            vec!["Finite.Part.owner", "Finite.Part.quantity"],
        ),
    ] {
        let e = example(false, body);
        let mut g = graph(&e);
        let a = architecture(&g, "a");
        let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet()).unwrap();
        let Part::Equation(E::Context { dependencies, .. }) = data(&g, d.context.unwrap()).part()
        else {
            panic!("context")
        };
        for field in expected {
            assert!(dependencies.iter().any(|(r,f)| f==field && matches!(g.scalar(*r).unwrap(), Scalar::Subject {snapshot, subject,..} if snapshot=="v" && subject=="p")), "{body}: {field} missing from {dependencies:?}");
        }
        assert!(!dependencies.iter().any(
            |(r, _)| matches!(g.scalar(*r).unwrap(), Scalar::Subject {subject,..} if subject=="q")
        ));
        if body.contains("positive") {
            assert_eq!(d.status, EquationPresentationStatus::UnsupportedAlgorithm);
            assert!(d.rings.is_empty() && d.presentations.is_empty());
        } else {
            assert_eq!(d.rings.len(), 1);
            let Part::Ring { variables, .. } = data(&g, d.rings[0]).part() else {
                panic!("ring")
            };
            assert!(
                variables
                    .iter()
                    .all(|v| v.field.field.as_deref() == Some("Finite.Part.quantity"))
            );
        }
        replay(&e, &g.nodes, &g.contexts).unwrap();
    }
}

#[test]
fn context_keeps_bool_guard_reads_without_turning_them_into_numeric_variables() {
    use crate::observed::equation_presentation_node::Part as E;
    let definition = DEFINITION.replace(r#""fields":[{"name":"quantity""#,r#""fields":[{"name":"enabled","type":"Bool","meaning":"条件の元観測。"},{"name":"quantity""#);
    let map = MAP.replace(r#""atoms":["#, r#""atoms":[{"id":"pe","subject":"p","field":"Finite.Part.enabled","value":true,"origin":"model"},{"id":"qe","subject":"q","field":"Finite.Part.enabled","value":false,"origin":"model"},"#);
    let e = evaluate_observed_bytes(
        custom_sources(
            &definition,
            &map,
            "law required gated(c:Part) when c.enabled:c.quantity=0;",
        ),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &mut quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet()).unwrap();
    let Part::Equation(E::Context { dependencies, .. }) = data(&g, d.context.unwrap()).part()
    else {
        panic!("context")
    };
    for field in ["Finite.Part.enabled", "Finite.Part.quantity"] {
        assert!(
            dependencies.iter().any(|(r, f)| f == field
                && matches!(g.scalar(*r).unwrap(),Scalar::Subject {subject,..} if subject=="p")),
            "{field}: {dependencies:?}"
        );
    }
    let Part::Ring { variables, .. } = data(&g, d.rings[0]).part() else {
        panic!("ring")
    };
    assert!(
        variables
            .iter()
            .all(|v| v.field.field.as_deref() == Some("Finite.Part.quantity"))
    );
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn finite_missing_completions_keep_one_formal_coordinate_and_never_supply_actual_epsilon() {
    use crate::observed::equation_presentation_node::Part as E;
    for missing in [false, true] {
        let definition = DEFINITION.replace(r#""type":"Z""#, r#""type":["Fp","2"]"#);
        let map = if missing {
            MAP.replace(r#",{"id":"qx","subject":"q","field":"Finite.Part.quantity","value":"1","origin":"model"}"#,"")
        } else {
            MAP.into()
        };
        let e = evaluate_observed_bytes(
            custom_sources(&definition, &map, BODY),
            &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
            &mut quiet(),
        )
        .unwrap();
        let mut g = graph(&e);
        let b = architecture(&g, "b");
        let d = retain(&mut g, e.prepared.shared_inputs(), b, 0, &mut quiet()).unwrap();
        assert_eq!(d.coordinates.len(), if missing { 4 } else { 2 });
        if missing {
            for instance in [0, 1] {
                assert_eq!(
                    d.coordinates
                        .iter()
                        .filter(|q| q.position.instance == instance)
                        .map(|q| q.case)
                        .collect::<Vec<_>>(),
                    vec![0, 1]
                );
            }
        }
        let p = d.presentations[0].unwrap();
        let Part::Equation(E::Presentation {
            coordinates,
            evaluation,
            ..
        }) = data(&g, p).part()
        else {
            panic!("presentation")
        };
        assert_eq!(coordinates.len(), 2);
        assert_eq!(
            coordinates
                .iter()
                .map(|q| (q.instance.0, q.component.clone()))
                .collect::<std::collections::BTreeSet<_>>()
                .len(),
            2
        );
        assert_eq!(evaluation.is_none(), missing);
        for q in coordinates {
            assert_eq!(q.epsilon.is_none(), missing);
            if !missing {
                let original = d
                    .originals
                    .iter()
                    .find(|o| o.reference == q.instance)
                    .unwrap();
                let name = &data(&g, p).source.architecture.readings().instances()
                    [original.instance]
                    .declaration()
                    .name;
                let expected = if name == "Chosen.zero" {
                    vec![(Json::str("1"), vec![0])]
                } else {
                    assert_eq!(name, "Chosen.one");
                    vec![]
                };
                assert_eq!(terms(&g, q.epsilon.unwrap()), expected);
            }
        }
        assert_eq!(g.nodes[p.0].reasons.is_empty(), !missing);
        if missing {
            assert_eq!(
                g.nodes[p.0].reasons[0].missing[0].field.as_deref(),
                Some("Finite.Part.quantity")
            );
        }
        replay(&e, &g.nodes, &g.contexts).unwrap();
    }
}

#[test]
fn missing_bool_completions_keep_original_cases_and_do_not_promote_branch_values() {
    use crate::observed::equation_presentation_node::Part as E;
    let definition=DEFINITION.replace(r#""fields":[{"name":"quantity""#,r#""fields":[{"name":"enabled","type":"Bool","meaning":"条件の元観測。"},{"name":"quantity""#);
    let map=MAP.replace(r#""atoms":["#,r#""atoms":[{"id":"pe","subject":"p","field":"Finite.Part.enabled","value":true,"origin":"model"},"#);
    for (body, uniform) in [
        (
            "law required used(c:Part):let discarded=c.enabled in c.quantity=0;",
            true,
        ),
        (
            "law required choose(c:Part):c.quantity=(if c.enabled then 0 else 1);",
            false,
        ),
    ] {
        let e = evaluate_observed_bytes(
            custom_sources(&definition, &map, body),
            &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
            &mut quiet(),
        )
        .unwrap();
        let mut g = graph(&e);
        let b = architecture(&g, "b");
        let d = retain(&mut g, e.prepared.shared_inputs(), b, 0, &mut quiet()).unwrap();
        assert_eq!(d.coordinates.len(), 2);
        assert_eq!(
            d.coordinates.iter().map(|q| q.case).collect::<Vec<_>>(),
            vec![0, 1]
        );
        assert_eq!(
            d.status,
            if uniform {
                EquationPresentationStatus::Ready
            } else {
                EquationPresentationStatus::UnsupportedAlgorithm
            }
        );
        let core = data(&g, d.context.unwrap()).source.core.as_ref().unwrap();
        assert!(core.occurrences().iter().all(|q| q.nu.is_some() == uniform));
        if uniform {
            assert_eq!(core.occurrences()[0].nu, core.occurrences()[1].nu);
        }
        if uniform {
            let p = d.presentations[0].unwrap();
            let Part::Equation(E::Presentation {
                coordinates,
                evaluation,
                ..
            }) = data(&g, p).part()
            else {
                panic!("presentation")
            };
            assert_eq!(coordinates.len(), 1);
            assert_eq!(
                terms(
                    &g,
                    coordinates[0]
                        .epsilon
                        .expect("original observed body is already known")
                ),
                vec![(Json::str("1"), vec![0])]
            );
            assert!(
                evaluation.is_some(),
                "numeric symbols are observed independently of the Bool read"
            );
            assert!(g.nodes[p.0].reasons.is_empty());
            let Part::Equation(E::Context { dependencies, .. }) =
                data(&g, d.context.unwrap()).part()
            else {
                panic!("context")
            };
            assert!(
                dependencies
                    .iter()
                    .any(|(_, field)| field == "Finite.Part.enabled")
            );
        } else {
            assert_eq!(d.presentations, vec![None]);
        }
        replay(&e, &g.nodes, &g.contexts).unwrap();
    }
}

#[test]
fn a_missing_parameter_row_does_not_erase_another_rows_observed_epsilon() {
    use crate::observed::equation_presentation_node::Part as E;
    let definition = DEFINITION.replace(r#""type":"Z""#, r#""type":["Fp","2"]"#);
    let map = MAP.replace(
        r#",{"id":"qx","subject":"q","field":"Finite.Part.quantity","value":"1","origin":"model"}"#,
        "",
    );
    let e = evaluate_observed_bytes(
        custom_sources(
            &definition,
            &map,
            "law required choose(c:Part,b:Bool):0=(if b then c.quantity else 0);",
        ),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &mut quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let b = architecture(&g, "b");
    let d = retain(&mut g, e.prepared.shared_inputs(), b, 0, &mut quiet()).unwrap();
    let p = d.presentations[0].unwrap();
    let Part::Equation(E::Presentation {
        coordinates,
        evaluation,
        ..
    }) = data(&g, p).part()
    else {
        panic!("presentation")
    };
    assert!(evaluation.is_none());
    assert_eq!(coordinates.len(), 2);
    for q in coordinates {
        let original = d
            .originals
            .iter()
            .find(|o| o.reference == q.instance)
            .unwrap();
        let parameter = original.bindings.iter().find(|b| b.name == "b").unwrap();
        match g.scalar(parameter.value).unwrap() {
            Scalar::Bool(false) => {
                assert!(terms(&g, q.epsilon.expect("known false row epsilon")).is_empty())
            }
            Scalar::Bool(true) => assert!(q.epsilon.is_none()),
            _ => panic!("Bool parameter"),
        }
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn global_equation_context_keeps_same_subject_ids_in_different_snapshots_and_their_modes() {
    use crate::observed::equation_presentation_node::Part as E;
    let map=format!(r#"{},{{"id":"w","origin":"external","subjects":[{{"id":"a","type":"Finite.Root","origin":"external"}}],"atoms":[]}}]}}"#,MAP.strip_suffix("]}").unwrap()).replace(r#""origins":["#,r#""origins":[{"id":"external","mode":"proposed","method":"独立の原始参照。","locations":[],"note":"別snapshotの同名subject。"},"#);
    let e = evaluate_observed_bytes(
        custom_sources(DEFINITION, &map, BODY),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &mut quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet()).unwrap();
    let ctx = d.context.unwrap();
    let Part::Equation(E::Context { carrier, .. }) = data(&g, ctx).part() else {
        panic!("context");
    };
    assert_eq!(carrier.len(), 13);
    for snapshot in ["v", "w"] {
        assert!(carrier.iter().any(|v|matches!(v,Scalar::Tuple(xs) if matches!((&xs[0],&xs[1],&xs[2],&xs[3]),(Scalar::Text(s),Scalar::Text(id),Scalar::Option{value:None,..},Scalar::Option{value:None,..}) if s==snapshot&&id=="a"))));
    }
    for reference in [ctx, d.presentations[0].unwrap()] {
        let node = g.get(reference).unwrap();
        assert!(node.scope.snapshots.contains("w"));
        assert!(node.scope.modes.contains("proposed"));
        assert!(
            node.support
                .iter()
                .any(|f| f.snapshot == "w" && f.subject == "a" && f.field.is_none())
        );
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn source_only_unimplemented_parameter_keeps_original_scope_without_fake_context_or_presentation() {
    let e = example(false, "law required parameter(c:Part,k:Z):c.quantity=k;");
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet()).unwrap();
    assert_eq!(d.status, EquationPresentationStatus::Undetermined);
    assert!(d.unavailable.as_ref().unwrap().feature.contains("未実装"));
    assert!(d.context.is_none());
    assert!(d.presentations.is_empty());
    let original = d.originals.iter().find(|o| o.row.is_none()).unwrap();
    let qs = &g.get(original.reference).unwrap().scope.quantifiers;
    assert!(
        qs.iter().any(|q| q.name == "k"
            && q.ty == Type::Z
            && q.kind == crate::law::ast::QuantKind::Forall)
    );
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn finite_parameter_rows_are_distinct_presentation_instances_without_requantifying_the_template() {
    use crate::observed::equation_presentation_node::Part as E;
    let e = example(
        false,
        "law required parameter(c:Part,b:Bool):c.quantity=(if b then 0 else 1);",
    );
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet()).unwrap();
    let r = d.presentations[0].unwrap();
    let Part::Equation(E::Presentation {
        instances,
        coordinates,
        ..
    }) = data(&g, r).part()
    else {
        panic!("presentation");
    };
    assert_eq!(instances.len(), 2);
    assert_eq!(coordinates.len(), 2);
    assert_ne!(instances[0], instances[1]);
    let mut booleans = vec![];
    for reference in instances {
        let original = d
            .originals
            .iter()
            .find(|o| o.reference == *reference)
            .unwrap();
        assert!(original.row.is_some());
        let binding = original.bindings.iter().find(|b| b.name == "b").unwrap();
        let Scalar::Bool(value) = g.scalar(binding.value).unwrap() else {
            panic!("boolean parameter");
        };
        booleans.push(*value);
        assert!(g.get(*reference).unwrap().scope.quantifiers.is_empty());
    }
    booleans.sort();
    assert_eq!(booleans, [false, true]);
    let template = d.originals.iter().find(|o| o.row.is_none()).unwrap();
    assert!(!instances.contains(&template.reference));
    assert!(
        g.get(template.reference)
            .unwrap()
            .scope
            .quantifiers
            .iter()
            .any(|q| q.name == "b" && q.ty == Type::Bool)
    );
    let Part::Equation(E::Context { laws, .. }) = data(&g, d.context.unwrap()).part() else {
        panic!("context");
    };
    assert_eq!(laws, instances);
    assert!(g.get(r).unwrap().scope.quantifiers.is_empty());
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn polynomial_presentation_recheck_rejects_derived_coordinate_ring_ideal_and_context_changes() {
    use crate::observed::equation_presentation_node::Part as E;
    let e = example(false, BODY);
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet()).unwrap();
    let r = d.presentations[0].unwrap();
    for kind in 0..8 {
        let at = if kind < 2 { d.context.unwrap() } else { r };
        let mut nodes = g.nodes.clone();
        let Some(Payload::Construction(value)) = &mut nodes[at.0].payload else {
            panic!("native");
        };
        let D::PolynomialLaw(value) = &mut value.data else {
            panic!("polynomial");
        };
        let mut source = (*value.source).clone();
        let Part::Equation(part) = &mut source.parts[value.index] else {
            panic!("equation");
        };
        match part {
            E::Context {
                carrier,
                dependencies,
                ..
            } => {
                if kind == 0 {
                    carrier.pop();
                } else {
                    dependencies.clear();
                }
            }
            E::Presentation {
                coordinates,
                ring,
                required,
                evaluation,
                context,
                ..
            } => match kind {
                2 => *ring = d.bases[0],
                3 => *required = d.coordinates[0].witness.unwrap(),
                4 => coordinates[0].epsilon = Some(coordinates[0].nu),
                5 => {
                    let q = &mut coordinates[0];
                    std::mem::swap(&mut q.lhs, &mut q.rhs)
                }
                6 => *evaluation = None,
                _ => *context = d.domains[0],
            },
        }
        value.source = Arc::new(source);
        assert!(replay(&e, &nodes, &g.contexts).is_err(), "change {kind}");
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn progressive_missing_match_discovery_keeps_observed_roots_separate_from_cases() {
    use crate::observed::equation_presentation_node::Part as E;
    let definition = DEFINITION.replace(r#""type":"Z""#, r#""type":["Fp","2"]"#).replace(r#""fields":[{"name":"quantity""#, r#""fields":[{"name":"enabled","type":"Bool","meaning":"条件の元観測。"},{"name":"quantity""#);
    let map = MAP.replace(r#""atoms":["#, r#""atoms":[{"id":"pe","subject":"p","field":"Finite.Part.enabled","value":true,"origin":"model"},"#).replace(
        r#",{"id":"qx","subject":"q","field":"Finite.Part.quantity","value":"1","origin":"model"}"#,
        "",
    );
    let e = evaluate_observed_bytes(
        custom_sources(
            &definition,
            &map,
            "law required linked(c:Part):match c.enabled { ignored => c.quantity=0; };",
        ),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &mut quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let b = architecture(&g, "b");
    let d = retain(&mut g, e.prepared.shared_inputs(), b, 0, &mut quiet()).unwrap();
    assert!(!d.coordinates.is_empty());
    assert_eq!(d.status, EquationPresentationStatus::Undetermined);
    let core = data(&g, d.context.unwrap()).source.core.as_ref().unwrap();
    let source = core
        .base()
        .base()
        .evaluations()
        .iter()
        .find(|s| s.position().object == 0)
        .unwrap();
    let crate::observed::object_evaluate::ObjectEvaluationOutcome::Evaluated(original) =
        source.evaluation().outcome()
    else {
        panic!("evaluation")
    };
    assert!(original.nodes.iter().any(|n| matches!(&n.payload,Some(Payload::CompletionSeed{roots,..}) if roots.iter().filter(|r|matches!(original.nodes[r.0].ty,NodeType::Evaluation(Type::Bool))).count()>1)),"fixture must discover another slot during a completion case");
    for p in d.presentations.iter().flatten() {
        let Part::Equation(E::Presentation { coordinates, .. }) = data(&g, *p).part() else {
            panic!("presentation")
        };
        assert!(coordinates.iter().all(|q| q.epsilon.is_none()));
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn native_law_expression_frames_reject_corrupted_original_body_and_guard_ids_without_panicking() {
    let e = example(false, "law required zero(c:Part) when true:c.quantity=0;");
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let diagram = retain(&mut g, e.prepared.shared_inputs(), a, 0, &mut quiet()).unwrap();
    let origin = diagram.readings[0].instance;
    let env = Environment::with_requests(
        e.prepared.inputs(),
        e.prepared.requests().requests(),
        &mut quiet(),
    )
    .unwrap();
    let evaluated =
        crate::observed::law_evaluation::evaluate(&env, &mut g, origin, a, &mut quiet()).unwrap();
    let index = evaluated.instance.unwrap();
    let body = evaluated.body.unwrap();
    let Some(Payload::Evaluation { expression, .. }) = &g.nodes[body.0].payload else {
        panic!("Evaluation")
    };
    let Some(Payload::Expression {
        location: crate::issue::Location::Law { span },
        ..
    }) = &g.nodes[expression.0].payload
    else {
        panic!("Source")
    };
    let span = *span;
    let original = data(&g, origin).source.clone();
    for guard in [false, true] {
        let mut changed = (*original).clone();
        let Part::LawInstance {
            body: source_body,
            guard: condition,
            ..
        } = &changed.parts[origin.0 - changed.base]
        else {
            panic!("LawInstance")
        };
        let r = if guard {
            condition.unwrap()
        } else {
            *source_body
        };
        let Part::Source { expression, .. } = &mut changed.parts[r.0 - changed.base] else {
            panic!("Source")
        };
        *expression = usize::MAX;
        let mut bad = Graph::new(&quiet());
        bad.nodes = g.nodes.clone();
        bad.contexts = g.contexts.clone();
        bad.requests = g.requests.clone();
        bad.checked_answers = g.checked_answers.clone();
        bad.frames = g.frames.clone();
        bad.iterations = g.iterations.clone();
        bad.instances = g.instances.clone();
        bad.cases = g.cases.clone();
        bad.universal_witnesses = g.universal_witnesses.clone();
        let Some(Payload::Construction(v)) = &mut bad.nodes[origin.0].payload else {
            panic!("native")
        };
        let D::PolynomialLaw(d) = &mut v.data else {
            panic!("polynomial")
        };
        d.source = Arc::new(changed);
        assert!(
            crate::observed::law_evaluation::body_guard(&bad, index, span, bad.nodes.len())
                .is_err()
        );
        assert!(env.recheck_node(&bad, &bad.nodes[body.0], body.0).is_err());
    }
}
