use super::*;
use crate::control::quiet;
use crate::{input::InputSources, observed::evaluate_observed_bytes};
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

const BODY: &str = "law required part(c:Part,n:Fp(2)):c.quantity=n;law optional root(a:Root):true;law optional fixed():true;";
fn example(body: &str) -> ObservedEvaluation {
    evaluate_observed_bytes(
        custom_sources(DEFINITION, MAP, body),
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
    NodeRef(g.nodes.iter().position(|n| matches!(&n.payload,Some(Payload::Construction(v)) if matches!((&v.witness,&v.data),(Witness::Architecture(a),D::Architecture{..}) if a.construction().root().subject==root))).unwrap())
}
fn data(g: &Graph, r: NodeRef) -> &Data {
    let Some(Payload::Construction(v)) = &g.nodes[r.0].payload else {
        panic!("native")
    };
    let D::ObjectComponents(d) = &v.data else {
        panic!("objects")
    };
    d
}
fn property(g: &Graph, r: NodeRef, k: &str) -> Json {
    let Json::Obj(ref o) = data(g, r).wire() else {
        panic!("object")
    };
    o[k].clone()
}
#[test]
fn base_and_owned_keep_equal_configurations_as_distinct_objects_and_applicable_laws() {
    let e = example(BODY);
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let start = g.nodes.len();
    let result = retain(&mut g, e.prepared.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(result.objects.len(), 2);
    assert_eq!(result.architectures[0], a);
    assert_eq!(result.base, result.objects[0]);
    assert_ne!(result.objects[0], result.objects[1]);
    for (index, object) in result.objects.iter().enumerate() {
        assert_eq!(
            g.get(*object).unwrap().ty,
            NodeType::Construction(T::ObjectComponent)
        );
        assert_eq!(
            property(&g, *object, "kind"),
            Json::str(if index == 0 { "base" } else { "owned" })
        );
        assert_eq!(
            property(&g, *object, "object"),
            result.architectures[index].wire()
        );
        let Part::Component { subject, .. } = data(&g, *object).part() else {
            panic!("component")
        };
        assert!(
            matches!(g.scalar(*subject).unwrap(),Scalar::Subject{subject,..}if subject==if index==0{"a"}else{"p"})
        );
    }
    let Part::Architecture {
        root,
        configuration,
        laws,
        ..
    } = data(&g, result.architectures[1]).part()
    else {
        panic!("part")
    };
    assert!(matches!(g.scalar(*root).unwrap(),Scalar::Subject{subject,..}if subject=="p"));
    let Part::Configuration(part) = data(&g, *configuration).part() else {
        panic!("config")
    };
    let Some(Payload::Construction(v)) = &g.get(a).unwrap().payload else {
        panic!("native")
    };
    let Witness::Architecture(w) = &v.witness else {
        panic!("witness")
    };
    assert_eq!(Some(part), w.construction().base().configuration());
    assert_eq!(laws.len(), 1);
    let names = laws
        .iter()
        .map(|r| {
            let Some(Payload::Construction(v)) = &g.get(*r).unwrap().payload else {
                panic!("law")
            };
            let D::LawInstance { instance, .. } = v.data else {
                panic!("instance")
            };
            w.readings().instances()[instance]
                .declaration()
                .name
                .clone()
        })
        .collect::<Vec<_>>();
    assert_eq!(names, ["Chosen.part"]);
    let Some(Payload::Construction(v)) = &g.get(laws[0]).unwrap().payload else {
        panic!("law")
    };
    let D::LawInstance { instance, .. } = v.data else {
        panic!("instance")
    };
    assert_eq!(w.readings().instances()[instance].parameters()[0].name, "n");
    assert_eq!(
        w.readings().instances()[instance].parameters()[0].ty,
        crate::types::Type::Fp("2".into())
    );
    for (index, node) in g.nodes.iter().enumerate().skip(start) {
        assert!(node.arguments.iter().all(|r| r.0 < index));
        assert_eq!(node.support, g.get(a).unwrap().support);
        let mut expected_scope = g.get(a).unwrap().scope.clone();
        if let Part::Reading { quantifiers, .. } = data(&g, NodeRef(index)).part() {
            expected_scope.quantifiers.extend_from_slice(quantifiers);
        }
        assert_eq!(node.scope, expected_scope);
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

const EXTENDED_DEFINITION: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Finite","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Finite.Root","meaning":"有限入力の対象。","parameters":[],"fields":[],"alignments":[]},{"kind":"entity","name":"Finite.Part","meaning":"有限入力の対象。","parameters":[{"name":"owner","type":["Ref","Finite.Root"],"meaning":"元の型付き値。"}],"fields":[{"name":"quantity","type":["Fp","2"],"meaning":"元の型付き値。"},{"name":"peer","type":["Option",["Ref","Finite.Part"]],"meaning":"固定された外部参照。"}],"alignments":[]},{"kind":"correspondence","name":"Finite.Migration","meaning":"有限入力の対象。","parameters":[{"name":"from","type":["Ref","Finite.Root"],"meaning":"元の型付き値。"},{"name":"to","type":["Ref","Finite.Root"],"meaning":"元の型付き値。"}],"fields":[{"name":"states","type":["Map",["Owned","Finite.Part","from"],["Owned","Finite.Part","to"]],"meaning":"元の型付き値。"},{"name":"hops","type":["Map",["Owned","Finite.Hop","from"],["Owned","Finite.Hop","to"]],"meaning":"元のarrow対応。"}],"alignments":[]},{"kind":"arrow","name":"Finite.Hop","meaning":"内部の生成操作。","parameters":[{"name":"owner","type":["Ref","Finite.Root"],"meaning":"包含対象。"},{"name":"from","type":["Owned","Finite.Part","owner"],"meaning":"元の始点。"},{"name":"to","type":["Owned","Finite.Part","owner"],"meaning":"元の終点。"}],"fields":[],"alignments":[]}]}]}"#;
const EXTENDED_MAP: &str = r#"{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{"namespace":"Finite","version":"1","digest":"@DIGEST@"}],"sources":[],"origins":[{"id":"model","mode":"specification","method":"独立の有限入力。","locations":[],"note":"原始値と対応だけを記録する。"}],"snapshots":[{"id":"v","origin":"model","subjects":[{"id":"a","type":"Finite.Root","origin":"model"},{"id":"b","type":"Finite.Root","origin":"model"},{"id":"p","type":"Finite.Part","origin":"model"},{"id":"q","type":"Finite.Part","origin":"model"},{"id":"m","type":"Finite.Migration","origin":"model"},{"id":"r","type":"Finite.Part","origin":"model"},{"id":"e","type":"Finite.Hop","origin":"model"}],"atoms":[{"id":"po","subject":"p","field":"Finite.Part.owner","value":["v","a"],"origin":"model"},{"id":"qo","subject":"q","field":"Finite.Part.owner","value":["v","b"],"origin":"model"},{"id":"px","subject":"p","field":"Finite.Part.quantity","value":"0","origin":"model"},{"id":"mx","subject":"m","field":"Finite.Migration.from","value":["v","a"],"origin":"model"},{"id":"my","subject":"m","field":"Finite.Migration.to","value":["v","a"],"origin":"model"},{"id":"mm","subject":"m","field":"Finite.Migration.states","value":[[["v","p"],["v","p"]],[["v","r"],["v","r"]]],"origin":"model"},{"id":"qx","subject":"q","field":"Finite.Part.quantity","value":"1","origin":"model"},{"id":"ro","subject":"r","field":"Finite.Part.owner","value":["v","a"],"origin":"model"},{"id":"rx","subject":"r","field":"Finite.Part.quantity","value":"0","origin":"model"},{"id":"pp","subject":"p","field":"Finite.Part.peer","value":{"some":["v","q"]},"origin":"model"},{"id":"rp","subject":"r","field":"Finite.Part.peer","value":{"none":true},"origin":"model"},{"id":"qp","subject":"q","field":"Finite.Part.peer","value":{"none":true},"origin":"model"},{"id":"eo","subject":"e","field":"Finite.Hop.owner","value":["v","a"],"origin":"model"},{"id":"ef","subject":"e","field":"Finite.Hop.from","value":["v","p"],"origin":"model"},{"id":"et","subject":"e","field":"Finite.Hop.to","value":["v","r"],"origin":"model"},{"id":"mh","subject":"m","field":"Finite.Migration.hops","value":[[["v","e"],["v","e"]]],"origin":"model"}]}]}"#;
fn extended(map: &str) -> ObservedEvaluation {
    evaluate_observed_bytes(
        custom_sources(
            EXTENDED_DEFINITION,
            map,
            &format!("{BODY}law optional hop(h:Hop):true;"),
        ),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &mut quiet(),
    )
    .unwrap()
}
fn fact(subject: &str, field: Option<&str>, atom: Option<&str>) -> Fact {
    Fact {
        snapshot: "v".into(),
        subject: subject.into(),
        field: field.map(Into::into),
        atom: atom.map(str::to_owned),
    }
}
fn family_configuration(g: &Graph, r: NodeRef) -> &Configuration {
    let Part::Architecture { configuration, .. } = data(g, r).part() else {
        panic!("architecture")
    };
    let Part::Configuration(c) = data(g, *configuration).part() else {
        panic!("config")
    };
    c
}
#[test]
fn owned_subjects_keep_external_existence_relations_and_exclude_arrows_and_foreign_fields() {
    let e = extended(EXTENDED_MAP);
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let result = retain(&mut g, e.prepared.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(result.objects.len(), 3);
    let subjects = result
        .objects
        .iter()
        .map(|r| {
            let Part::Component { subject, .. } = data(&g, *r).part() else {
                panic!("object")
            };
            let Scalar::Subject { subject, .. } = g.scalar(*subject).unwrap() else {
                panic!("ref")
            };
            subject.as_str()
        })
        .collect::<Vec<_>>();
    assert_eq!(subjects, ["a", "p", "r"]);
    let p = family_configuration(&g, result.architectures[1]);
    let (a0, p0, q0, po, px, pp) = (
        fact("a", None, None),
        fact("p", None, None),
        fact("q", None, None),
        fact("p", Some("Finite.Part.owner"), Some("po")),
        fact("p", Some("Finite.Part.quantity"), Some("px")),
        fact("p", Some("Finite.Part.peer"), Some("pp")),
    );
    let expected = std::collections::BTreeSet::from([
        a0.clone(),
        p0.clone(),
        q0.clone(),
        po.clone(),
        px.clone(),
        pp.clone(),
    ]);
    assert_eq!(
        p.family()
            .iter()
            .cloned()
            .collect::<std::collections::BTreeSet<_>>(),
        expected
    );
    assert_eq!(
        p.relations()
            .iter()
            .cloned()
            .collect::<std::collections::BTreeSet<_>>(),
        std::collections::BTreeSet::from([
            (p0.clone(), po.clone()),
            (p0.clone(), px.clone()),
            (p0.clone(), pp.clone()),
            (po, a0),
            (pp, q0)
        ])
    );
    assert_eq!(
        p.identifications()
            .iter()
            .cloned()
            .collect::<std::collections::BTreeSet<_>>(),
        expected.iter().map(|f| (f.clone(), f.clone())).collect()
    );
    assert_eq!(
        p.requirements()
            .iter()
            .cloned()
            .collect::<std::collections::BTreeSet<_>>(),
        std::collections::BTreeSet::from([
            fact("p", Some("Finite.Part.owner"), None),
            fact("p", Some("Finite.Part.quantity"), None),
            fact("p", Some("Finite.Part.peer"), None),
            fact("q", Some("Finite.Part.owner"), None),
            fact("q", Some("Finite.Part.quantity"), None),
            fact("q", Some("Finite.Part.peer"), None)
        ])
    );
    let r = family_configuration(&g, result.architectures[2]);
    assert!(
        !r.family()
            .iter()
            .any(|f| f.subject == "q" || f.subject == "p" || f.subject == "e")
    );
    assert_ne!(p, r);
    for arch in result.architectures.iter().skip(1) {
        assert_eq!(property(&g, *arch, "internal_arrows"), Json::Arr(vec![]));
        let Part::Architecture { laws, .. } = data(&g, *arch).part() else {
            panic!("part")
        };
        assert_eq!(laws.len(), 1);
        let Some(Payload::Construction(v)) = &g.get(laws[0]).unwrap().payload else {
            panic!("law")
        };
        let D::LawInstance { bindings, .. } = &v.data else {
            panic!("instance")
        };
        assert_eq!(bindings.len(), 1);
        let Scalar::Subject { subject, .. } = g.scalar(bindings[0].value).unwrap() else {
            panic!("binding")
        };
        let Part::Architecture { root, .. } = data(&g, *arch).part() else {
            panic!("root")
        };
        assert!(matches!(g.scalar(*root).unwrap(),Scalar::Subject{subject:r,..}if subject==r));
    }
    let Some(Payload::Construction(v)) = &g.get(a).unwrap().payload else {
        panic!("native")
    };
    let D::Architecture { arrows, .. } = &v.data else {
        panic!("base")
    };
    assert_eq!(arrows.len(), 1);
    assert!(matches!(g.scalar(arrows[0]).unwrap(),Scalar::Subject{subject,..}if subject=="e"));
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn missing_quantity_retains_original_requirements_without_fabricating_values_or_dropping_laws() {
    let map = EXTENDED_MAP.replace(
        r#",{"id":"px","subject":"p","field":"Finite.Part.quantity","value":"0","origin":"model"}"#,
        "",
    );
    assert_ne!(map, EXTENDED_MAP);
    let e = extended(&map);
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let result = retain(&mut g, e.prepared.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    let c = family_configuration(&g, result.architectures[1]);
    assert!(
        c.requirements()
            .contains(&fact("p", Some("Finite.Part.quantity"), None))
    );
    assert!(
        !c.family()
            .iter()
            .any(|f| f.subject == "p" && f.field.as_deref() == Some("Finite.Part.quantity"))
    );
    let Part::Architecture { laws, .. } = data(&g, result.architectures[1]).part() else {
        panic!("arch")
    };
    assert_eq!(laws.len(), 1);
    let source = &data(&g, result.base).source;
    assert!(
        source
            .parts
            .iter()
            .all(|p| !matches!(p,Part::Subject(v)if !matches!(v,Scalar::Subject{..})))
    );
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn unknown_owner_or_reference_never_promotes_a_conditional_configuration() {
    for (atom, field, value) in [
        ("po", "Finite.Part.owner", r#"["v","a"]"#),
        ("pp", "Finite.Part.peer", r#"{"some":["v","q"]}"#),
    ] {
        let old = format!(
            r#"{{"id":"{atom}","subject":"p","field":"{field}","value":{value},"origin":"model"}},"#
        );
        let map = EXTENDED_MAP.replace(&old, "");
        assert_ne!(map, EXTENDED_MAP);
        let e = extended(&map);
        let mut g = graph(&e);
        let (index, a) = g
            .nodes
            .iter()
            .enumerate()
            .find_map(|(i, n)| {
                let Some(Payload::Construction(v)) = &n.payload else {
                    return None;
                };
                let Witness::Architecture(a) = &v.witness else {
                    return None;
                };
                (a.construction().root().subject == "a").then_some((i, a.clone()))
            })
            .unwrap();
        let before = g.nodes.len();
        assert!(
            plan(
                e.prepared.inputs(),
                &a,
                NodeRef(index),
                NodeRef(index),
                &[],
                before,
                &mut quiet()
            )
            .unwrap()
            .is_none()
        );
        assert_eq!(g.nodes.len(), before);
        let pending=g.nodes.iter().enumerate().find_map(|(i,n)|{let Some(Payload::Construction(v))=&n.payload else{return None};matches!((&v.witness,&v.data),(Witness::Architecture(w),D::Pending{ty:T::Architecture,..})if Arc::ptr_eq(w,&a)).then_some(NodeRef(i))}).unwrap();
        assert!(retain(&mut g, e.prepared.shared_inputs(), pending, &mut quiet()).is_err());
        assert_eq!(g.nodes.len(), before);
        replay(&e, &g.nodes, &g.contexts).unwrap();
    }
}
#[test]
fn a_root_without_owned_entities_keeps_exactly_its_base_component() {
    let map = MAP
        .replace(
            r#""id":"po","subject":"p","field":"Finite.Part.owner","value":["v","a"]"#,
            r#""id":"po","subject":"p","field":"Finite.Part.owner","value":["v","b"]"#,
        )
        .replace(r#""value":[[["v","p"],["v","q"]]]"#, r#""value":[]"#);
    assert_ne!(map, MAP);
    let e = evaluate_observed_bytes(
        custom_sources(DEFINITION, &map, BODY),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &mut quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(d.objects, [d.base]);
    assert_eq!(d.architectures, [a]);
    assert_eq!(
        data(&g, d.base)
            .source
            .parts
            .iter()
            .filter(|p| matches!(p, Part::Component { .. }))
            .count(),
        1
    );
    assert_eq!(d.readings.len(), 1);
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn object_plans_reject_kind_subject_configuration_law_order_scope_and_output_forgery() {
    let e = extended(EXTENDED_MAP);
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    let source = data(&g, d.base).source.clone();
    let owned = d.objects[1].0 - source.base;
    let arch = d.architectures[1].0 - source.base;
    let Part::Architecture { configuration, .. } = source.parts[arch] else {
        panic!("arch")
    };
    let config = configuration.0 - source.base;
    let other = family_configuration(&g, d.architectures[2]).clone();
    for mode in 0..10 {
        let mut changed = (*source).clone();
        match mode {
            0 => {
                if let Part::Component { base, .. } = &mut changed.parts[owned] {
                    *base = true
                }
            }
            1 => {
                if let Part::Component { subject, .. } = &mut changed.parts[owned] {
                    *subject = source.root
                }
            }
            2 => {
                if let Part::Component { object, .. } = &mut changed.parts[owned] {
                    *object = source.reference
                }
            }
            3 => changed.parts[config] = Part::Configuration(other.clone()),
            4 => {
                if let Part::Architecture { laws, .. } = &mut changed.parts[arch] {
                    laws.clear()
                }
            }
            5 => {
                if let Part::Architecture { reading, .. } = &mut changed.parts[arch] {
                    *reading = "Other".into()
                }
            }
            6 => changed.outputs.objects.reverse(),
            7 => changed.support.clear(),
            8 => changed.scope.assignments = true,
            _ => changed.laws.reverse(),
        }
        assert!(
            changed
                .recheck(&g, e.prepared.inputs(), &source.architecture, &mut quiet())
                .is_err(),
            "mode {mode}"
        );
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn current_inputs_consumers_positions_and_cached_root_requests_are_rechecked() {
    let e = example(BODY);
    let mut g = graph(&e);
    let (a, b) = (architecture(&g, "a"), architecture(&g, "b"));
    let da = retain(&mut g, e.prepared.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    let db = retain(&mut g, e.prepared.shared_inputs(), b, &mut quiet())
        .unwrap()
        .unwrap();
    let env = Environment::with_requests(
        e.prepared.inputs(),
        e.prepared.requests().requests(),
        &mut quiet(),
    )
    .unwrap();
    for object in [da.base, db.base] {
        let n = g.get(object).unwrap().clone();
        env.recheck_node(&g, &n, object.0).unwrap();
    }
    assert_eq!(env.results.verified::<std::sync::Arc<crate::observed::object_component_diagram::Source>>().len(), 2);
    let original = g.get(da.objects[1]).unwrap().clone();
    let mut changed = original.clone();
    let Some(Payload::Construction(v)) = &mut changed.payload else {
        panic!("native")
    };
    let Some(Payload::Construction(foreign)) = &g.get(b).unwrap().payload else {
        panic!("foreign")
    };
    v.witness = foreign.witness.clone();
    assert!(env.recheck_node(&g, &changed, da.objects[1].0).is_err());
    let mut changed = original.clone();
    let Some(Payload::Construction(v)) = &mut changed.payload else {
        panic!("native")
    };
    let D::ObjectComponents(data) = &mut v.data else {
        panic!("objects")
    };
    data.index += 1;
    assert!(env.recheck_node(&g, &changed, da.objects[1].0).is_err());
    for field in 0..4 {
        let mut n = original.clone();
        match field {
            0 => n.ty = NodeType::Construction(T::Architecture),
            1 => n.arguments.reverse(),
            2 => n.support.clear(),
            _ => n.scope.assignments = true,
        }
        assert!(env.recheck_node(&g, &n, da.objects[1].0).is_err());
    }
    let e2 = example(&format!("{BODY} "));
    let other = Environment::with_requests(
        e2.prepared.inputs(),
        e.prepared.requests().requests(),
        &mut quiet(),
    )
    .unwrap();
    assert!(other.recheck_node(&g, &original, da.objects[1].0).is_err());
    g.requests[0].text.push(' ');
    assert!(env.recheck_node(&g, &original, da.objects[1].0).is_err());
    g.requests[0].text.pop();
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
fn stopping(signal: crate::result::Signal, at: usize) -> Control {
    let seen = std::rc::Rc::new(std::cell::Cell::new(0));
    Control::new(move |p| {
        if p == Checkpoint::ObjectInstances {
            seen.set(seen.get() + 1)
        }
        (seen.get() >= at).then_some(signal)
    })
}
#[test]
fn signal_stops_do_not_return_an_unfinished_family_and_every_finished_prefix_replays() {
    let e = example(BODY);
    let count = std::rc::Rc::new(std::cell::Cell::new(0));
    let seen = count.clone();
    let mut c = Control::new(move |p| {
        if p == Checkpoint::ObjectInstances {
            seen.set(seen.get() + 1)
        }
        None
    });
    let mut complete = graph(&e);
    let a = architecture(&complete, "a");
    let start = complete.nodes.len();
    retain(&mut complete, e.prepared.shared_inputs(), a, &mut c)
        .unwrap()
        .unwrap();
    let total = count.get();
    assert!(total > 20);
    let mut saw_prefix = false;
    for signal in [crate::result::Signal::Int, crate::result::Signal::Term] {
        for at in [1, 5, total / 2, total - 2, total] {
            let mut g = graph(&e);
            let a = architecture(&g, "a");
            let before = g.nodes.clone();
            assert!(
                matches!(
                    retain(
                        &mut g,
                        e.prepared.shared_inputs(),
                        a,
                        &mut stopping(signal, at)
                    ),
                    Err(ValidationFailure::Stop(_))
                ),
                "{signal:?} at {at}/{total}"
            );
            assert_eq!(&g.nodes[..start], before.as_slice());
            saw_prefix |= g.nodes.len() > start;
            replay(&e, &g.nodes, &g.contexts).unwrap();
        }
    }
    assert!(saw_prefix);
}
#[test]
fn unbounded_scalar_parameters_and_the_whole_original_body_stay_symbolic() {
    let definition = DEFINITION.replace(r#"["Fp","2"]"#, r#""Z""#);
    let body = "law required quantity(c:Part,n:Z):let x=c.quantity in x=n;";
    let e = evaluate_observed_bytes(
        custom_sources(&definition, MAP, body),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &mut quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let before = g.nodes.clone();
    let d = retain(&mut g, e.prepared.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    let Part::Architecture { laws, .. } = data(&g, d.architectures[1]).part() else {
        panic!("part")
    };
    assert_eq!(laws.len(), 1);
    let Some(Payload::Construction(v)) = &g.get(laws[0]).unwrap().payload else {
        panic!("law")
    };
    let (Witness::Architecture(w), D::LawInstance { instance, body, .. }) = (&v.witness, &v.data)
    else {
        panic!("instance")
    };
    let row = &w.readings().instances()[*instance];
    assert_eq!(row.parameters().len(), 1);
    assert_eq!(row.parameters()[0].name, "n");
    assert_eq!(row.parameters()[0].ty, crate::types::Type::Z);
    let Some(Payload::Construction(v)) = &g.get(*body).unwrap().payload else {
        panic!("body")
    };
    let D::Source {
        parameters,
        location,
        ..
    } = &v.data
    else {
        panic!("source")
    };
    assert_eq!(parameters, &vec![("n".into(), crate::types::Type::Z)]);
    let crate::issue::Location::Law { span } = location else {
        panic!("location")
    };
    let raw = std::str::from_utf8(e.prepared.inputs().sources().law().bytes()).unwrap();
    assert_eq!(&raw[span.0..span.1], "let x=c.quantity in x=n");
    assert_eq!(&g.nodes[..before.len()], before.as_slice());
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn an_equal_configuration_from_another_reading_keeps_a_distinct_origin_and_cache_entry() {
    let defs =
        crate::definition::check_definitions(&[("definition0", DEFINITION.as_bytes())]).unwrap();
    let digest = &defs.vocabularies["Finite"].digest;
    let body = format!(
        "{BODY}}}reading Other{{use vocabulary Finite version \"1\" digest \"{digest}\";{BODY}"
    );
    let e = evaluate_observed_bytes(
        custom_sources(DEFINITION, MAP, &body),
        &[
            "m=map(Finite.Migration,on=@v/m,reading=Chosen)",
            "n=map(Finite.Migration,on=@v/m,reading=Other)",
        ],
        &mut quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let find = |reading: &str| {
        NodeRef(g.nodes.iter().position(|n|matches!(&n.payload,Some(Payload::Construction(v))if matches!((&v.witness,&v.data),(Witness::Architecture(a),D::Architecture{..})if a.construction().root().subject=="a"&&a.construction().reading()==reading))).unwrap())
    };
    let (a, b) = (find("Chosen"), find("Other"));
    g.active = g.context_at(a.0);
    let da = retain(&mut g, e.prepared.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    g.active = g.context_at(b.0);
    let db = retain(&mut g, e.prepared.shared_inputs(), b, &mut quiet())
        .unwrap()
        .unwrap();
    let sa = data(&g, da.base).source.clone();
    let sb = data(&g, db.base).source.clone();
    assert_eq!(
        sa.architecture.construction().base().configuration(),
        sb.architecture.construction().base().configuration()
    );
    assert!(!Arc::ptr_eq(&sa, &sb));
    assert_eq!(
        property(&g, da.architectures[1], "reading"),
        Json::str("Chosen")
    );
    assert_eq!(
        property(&g, db.architectures[1], "reading"),
        Json::str("Other")
    );
    g.active = g.context_at(a.0);
    assert!(
        sa.recheck(&g, e.prepared.inputs(), &sb.architecture, &mut quiet())
            .is_err()
    );
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn all_objects_keep_original_law_and_view_reading_expressions_bindings_types_and_full_parameters() {
    let e = example(
        "view quantity(c:Part,n:Z):Fp(2)=c.quantity;law required bounded(c:Part,b:Bool):c.quantity=c.quantity;law optional fixed():true;",
    );
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(d.objects.len(), 2);
    assert_eq!(d.readings.len(), 4);
    let mut pairs = std::collections::BTreeSet::new();
    for r in &d.readings {
        assert!(pairs.insert((r.object, r.instance)));
        let Part::Reading {
            object,
            declaration,
            parameters,
            bindings,
            returns,
            quantifiers,
        } = data(&g, r.expression).part()
        else {
            panic!("reading")
        };
        assert_eq!(*object, d.objects[r.object]);
        let (ty, params) = match declaration.as_str() {
            "Chosen.quantity" => (
                Type::Option(Box::new(Type::Fp("2".into()))),
                vec![("n".into(), Type::Z)],
            ),
            "Chosen.bounded" => (Type::Bool, vec![("b".into(), Type::Bool)]),
            _ => panic!("unexpected declaration"),
        };
        assert_eq!(returns, &ty);
        assert_eq!(parameters, &params);
        assert_eq!(g.nodes[r.expression.0].ty, NodeType::Expression(ty));
        assert_eq!(quantifiers.len(), params.len());
        assert_eq!(bindings.len(), 1);
        assert_eq!(bindings[0].name, "c");
        assert_eq!(bindings[0].ty, Type::Ref("Finite.Part".into()));
        assert_eq!(
            g.scalar(bindings[0].value).unwrap(),
            &Scalar::Subject {
                snapshot: "v".into(),
                subject: "p".into(),
                entity: "Finite.Part".into()
            }
        );
        let Json::Obj(ref wire) = data(&g, r.expression).wire() else {
            panic!("wire")
        };
        assert_eq!(wire["kind"], Json::str("object_reading"));
        assert_eq!(wire["object"], object.wire());
        assert_eq!(wire["declaration"], Json::str(declaration));
        assert_eq!(wire.len(), 6);
        assert!(g.nodes[r.expression.0].judgment.is_none());
        assert!(g.nodes[r.expression.0].reasons.is_empty());
    }
    let source = &data(&g, d.base).source;
    let view = source
        .architecture
        .readings()
        .instances()
        .iter()
        .position(|i| i.declaration().name == "Chosen.quantity")
        .unwrap();
    assert!(matches!(
        source.architecture.readings().instances()[view].applications()[0],
        InstanceApplication::Applicable { .. }
    ));
    assert!(matches!(
        source.architecture.readings().instances()[view].applications()[1],
        InstanceApplication::Applicable { .. }
    ));
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn missing_and_outside_readings_remain_expressions_without_fabricating_none_true_or_evaluation() {
    let map = MAP.replace(
        r#",{"id":"px","subject":"p","field":"Finite.Part.quantity","value":"0","origin":"model"}"#,
        "",
    );
    assert_ne!(map, MAP);
    let e = evaluate_observed_bytes(
        custom_sources(
            DEFINITION,
            &map,
            "view quantity(c:Part):Fp(2)=c.quantity;view marker(a:Root):Bool=true;law required root(a:Root):true;",
        ),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &mut quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let before = g.nodes.len();
    let d = retain(&mut g, e.prepared.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(d.readings.len(), 6);
    let source = &data(&g, d.base).source;
    let index = source
        .architecture
        .readings()
        .instances()
        .iter()
        .position(|i| i.declaration().name == "Chosen.root")
        .unwrap();
    assert!(matches!(
        source.architecture.readings().instances()[index].applications()[1],
        InstanceApplication::NotApplicable
    ));
    assert!(
        d.readings
            .iter()
            .any(|r| r.object == 1 && r.instance == index)
    );
    let marker = source
        .architecture
        .readings()
        .instances()
        .iter()
        .position(|i| i.declaration().name == "Chosen.marker")
        .unwrap();
    assert!(matches!(
        source.architecture.readings().instances()[marker].applications()[1],
        InstanceApplication::NotApplicable
    ));
    let outside = d
        .readings
        .iter()
        .find(|r| r.object == 1 && r.instance == marker)
        .unwrap();
    assert!(matches!(
        g.nodes[outside.expression.0].ty,
        NodeType::Expression(Type::Option(_))
    ));
    for n in &g.nodes[before..] {
        let Some(Payload::Construction(v)) = &n.payload else {
            panic!("native")
        };
        let D::ObjectComponents(data) = &v.data else {
            panic!("objects")
        };
        assert!(!matches!(
            data.part(),
            Part::Subject(Scalar::Bool(_) | Scalar::Option { .. } | Scalar::Fp { .. })
        ));
    }
    for r in &d.readings {
        assert!(matches!(
            data(&g, r.expression).part(),
            Part::Reading { .. }
        ));
        assert!(
            !g.nodes[r.expression.0]
                .support
                .iter()
                .any(|f| f.atom.as_deref() == Some("px"))
        );
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn symbolic_reading_quantifiers_and_all_source_fields_and_output_links_are_rechecked() {
    let e = example("law required symbolic(c:Part,k:Z):c.quantity=0;");
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(d.readings.len(), 2);
    let expression = d.readings[0].expression;
    let source = data(&g, expression).source.clone();
    let at = data(&g, expression).index;
    let Part::Reading { quantifiers, .. } = data(&g, expression).part() else {
        panic!("reading")
    };
    assert_eq!(quantifiers.len(), 1);
    let q = &quantifiers[0];
    assert_eq!(q.kind, crate::law::ast::QuantKind::Forall);
    assert_eq!((&q.name, &q.ty), (&"k".to_string(), &Type::Z));
    let raw = std::str::from_utf8(e.prepared.inputs().sources().law().bytes()).unwrap();
    assert_eq!(&raw[q.occurrence.0..q.occurrence.1], "k");
    assert!(q.domain.is_none() && q.context.is_none());
    for r in &d.readings {
        assert_eq!(
            g.nodes[r.expression.0].scope.quantifiers,
            quantifiers.clone()
        );
    }
    for mode in 0..11 {
        let mut changed = (*source).clone();
        match mode {
            0 => {
                if let Part::Reading { object, .. } = &mut changed.parts[at] {
                    *object = d.objects[1];
                }
            }
            1 => {
                if let Part::Reading { declaration, .. } = &mut changed.parts[at] {
                    *declaration = "Chosen.other".into();
                }
            }
            2 => {
                if let Part::Reading { parameters, .. } = &mut changed.parts[at] {
                    parameters.clear();
                }
            }
            3 => {
                if let Part::Reading { bindings, .. } = &mut changed.parts[at] {
                    bindings[0].value = a;
                }
            }
            4 => {
                if let Part::Reading { returns, .. } = &mut changed.parts[at] {
                    *returns = Type::Z;
                }
            }
            5 => {
                if let Part::Reading { quantifiers, .. } = &mut changed.parts[at] {
                    quantifiers.clear();
                }
            }
            6 => changed.outputs.readings.swap(0, 1),
            7 => changed.outputs.readings[0].object = 1,
            8 => changed.outputs.readings[0].instance = usize::MAX,
            9 => changed.outputs.readings[0].expression = a,
            _ => changed.outputs.readings.clear(),
        }
        assert!(
            changed
                .recheck(&g, e.prepared.inputs(), &source.architecture, &mut quiet())
                .is_err(),
            "mode {mode}"
        );
    }
    let mut nodes = g.nodes.clone();
    nodes[expression.0].scope.quantifiers.clear();
    assert!(replay(&e, &nodes, &g.contexts).is_err());
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn reading_parameter_domains_preserve_external_snapshot_subject_support_and_scope() {
    let map=format!(r#"{},{{"id":"w","origin":"external","subjects":[{{"id":"z","type":"Finite.Root","origin":"external"}}],"atoms":[]}}]}}"#,MAP.strip_suffix("]}").unwrap()).replace(r#""origins":["#,r#""origins":[{"id":"external","mode":"proposed","method":"独立の外部参照。","locations":[],"note":"型付きparameter域。"},"#);
    let e = evaluate_observed_bytes(
        custom_sources(
            DEFINITION,
            &map,
            "view roots(c:Part,x:(Root,Bool)):Bool=true;",
        ),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &mut quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(d.readings.len(), 2);
    for r in &d.readings {
        let n = &g.nodes[r.expression.0];
        assert!(
            n.support
                .iter()
                .any(|f| f.snapshot == "w" && f.subject == "z" && f.field.is_none())
        );
        assert!(n.scope.snapshots.contains("w"));
        assert!(n.scope.modes.contains("proposed"));
        assert!(matches!(n.ty, NodeType::Expression(Type::Option(_))));
    }
    let source = data(&g, d.base).source.clone();
    let mut changed = (*source).clone();
    changed.support.retain(|f| f.snapshot != "w");
    assert!(
        changed
            .recheck(&g, e.prepared.inputs(), &source.architecture, &mut quiet())
            .is_err()
    );
    let mut nodes = g.nodes.clone();
    nodes[d.readings[0].expression.0]
        .scope
        .snapshots
        .remove("w");
    assert!(replay(&e, &nodes, &g.contexts).is_err());
    replay(&e, &g.nodes, &g.contexts).unwrap();
}

#[test]
fn a_finished_object_producer_rechecks_from_another_request_without_allowing_foreign_creation() {
    let body = format!("{BODY} view no():Bool=false;");
    let e = evaluate_observed_bytes(
        custom_sources(DEFINITION, MAP, &body),
        &[
            "m=map(Finite.Migration,on=@v/m,reading=Chosen)",
            "idle=evaluate(Chosen.no)",
        ],
        &mut quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    g.active = g.context_at(a.0);
    let d = retain(&mut g, e.prepared.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    g.active = *e.contexts.last().unwrap();
    assert_eq!(g.active.request, 1);
    let env = Environment::with_requests(
        e.prepared.inputs(),
        e.prepared.requests().requests(),
        &mut quiet(),
    )
    .unwrap();
    let old = g.get(d.architectures[1]).unwrap().clone();
    let checked = env.recheck_node(&g, &old, d.architectures[1].0);
    assert!(checked.is_ok(), "{checked:?}");
    let before = g.nodes.clone();
    assert!(retain(&mut g, e.prepared.shared_inputs(), a, &mut quiet()).is_err());
    assert_eq!(g.nodes, before);
}
