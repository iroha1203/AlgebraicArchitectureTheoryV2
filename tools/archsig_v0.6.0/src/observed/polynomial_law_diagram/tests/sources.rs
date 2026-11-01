use super::*;
fn source_text(e: &ObservedEvaluation, g: &Graph, r: NodeRef) -> String {
    let Part::Source {
        location: crate::issue::Location::Law { span },
        ..
    } = data(g, r).part()
    else {
        panic!("source")
    };
    let bytes = &e.prepared.inputs().sources().law().bytes();
    std::str::from_utf8(&bytes[span.0..span.1]).unwrap().into()
}
#[test]
fn original_law_rows_keep_role_whole_source_exact_spans_bindings_and_typed_sides() {
    let e = example(false, BODY);
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &quiet()).unwrap();
    assert!(!d.originals.is_empty());
    for o in &d.originals {
        let Part::LawInstance {
            name,
            role,
            occurrence,
            bindings,
            body,
            guard,
            ..
        } = data(&g, o.reference).part()
        else {
            panic!("law")
        };
        let suffix = if name == "Chosen.zero" {
            assert_eq!(*role, Role::Required);
            "0"
        } else {
            assert_eq!(name, "Chosen.one");
            assert_eq!(*role, Role::Optional);
            "1"
        };
        assert_eq!(source_text(&e, &g, *body), format!("c.quantity={suffix}"));
        assert!(guard.is_none());
        assert!(o.parameters.is_empty());
        assert_eq!(bindings.len(), 1);
        assert_eq!(bindings[0].name, "c");
        assert_eq!(
            g.scalar(bindings[0].value).unwrap(),
            &Scalar::Subject {
                snapshot: "v".into(),
                subject: "p".into(),
                entity: "Finite.Part".into()
            }
        );
        let crate::issue::Location::Law { span } = occurrence else {
            panic!("occurrence")
        };
        let text =
            std::str::from_utf8(&e.prepared.inputs().sources().law().bytes()[span.0..span.1])
                .unwrap();
        assert_eq!(
            text,
            if suffix == "0" {
                "law required zero(c:Part):c.quantity=0;"
            } else {
                "law optional one(c:Part):c.quantity=1;"
            }
        );
    }
    for q in &d.coordinates {
        let o = d
            .originals
            .iter()
            .find(|o| o.reference == q.instance)
            .unwrap();
        assert_eq!((o.instance, o.row), (q.position.instance, q.row));
        assert_eq!(source_text(&e, &g, q.lhs), "c.quantity");
        assert!(matches!(source_text(&e, &g, q.rhs).as_str(), "0" | "1"));
        assert_eq!(g.nodes[q.lhs.0].ty, NodeType::Expression(Type::Z));
        assert_eq!(g.nodes[q.rhs.0].ty, NodeType::Expression(Type::Z));
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn lexical_let_and_match_are_closed_by_typed_substitution_before_tuple_projection() {
    let definition = DEFINITION.replace(r#""type":"Z""#, r#""type":["Tuple","Z","Q"]"#);
    let map = MAP
        .replace(r#""value":"0""#, r#""value":["0",["0","1"]]"#)
        .replace(r#""value":"1""#, r#""value":["1",["1","1"]]"#);
    let body = "law required pair(c:Part):let x=c.quantity in match x { y => y=(0,0); };";
    let e = evaluate_observed_bytes(
        custom_sources(&definition, &map, body),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &quiet()).unwrap();
    assert_eq!(d.coordinates.len(), 2);
    for (q, ty) in d.coordinates.iter().zip([Type::Z, Type::Q]) {
        let Part::Transform {
            operation: Transform::Project,
            operands,
            position,
            ..
        } = data(&g, q.lhs).part()
        else {
            panic!("project")
        };
        assert_eq!(*position, Some(q.component[0]));
        assert_eq!(g.nodes[q.lhs.0].ty, NodeType::Expression(ty.clone()));
        let Part::Transform {
            operation: Transform::Substitute,
            operands: source,
            bindings,
            ..
        } = data(&g, operands[0]).part()
        else {
            panic!("substitute")
        };
        assert_eq!(source_text(&e, &g, source[0]), "y");
        assert_eq!(
            bindings.iter().map(|b| b.name.as_str()).collect::<Vec<_>>(),
            ["x", "y"]
        );
        assert_eq!(source_text(&e, &g, bindings[0].value), "c.quantity");
        let Part::Transform {
            operation: Transform::Substitute,
            operands,
            ..
        } = data(&g, bindings[1].value).part()
        else {
            panic!("lexical y")
        };
        assert_eq!(source_text(&e, &g, operands[0]), "x");
        let original = d
            .originals
            .iter()
            .find(|o| o.reference == q.instance)
            .unwrap();
        assert_eq!(
            source_text(&e, &g, original.body),
            "let x=c.quantity in match x { y => y=(0,0); }"
        );
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn finite_parameter_rows_keep_actual_values_and_symbolic_instance_without_fake_empty_row() {
    let e = example(
        false,
        "law required parameter(c:Part,b:Bool):c.quantity=(if b then 0 else 1);",
    );
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &quiet()).unwrap();
    let symbolic = d
        .originals
        .iter()
        .filter(|o| o.row.is_none())
        .collect::<Vec<_>>();
    assert_eq!(symbolic.len(), 1);
    assert_eq!(symbolic[0].parameters, [("b".into(), Type::Bool)]);
    assert_eq!(symbolic[0].bindings.len(), 1);
    let rows = d
        .originals
        .iter()
        .filter(|o| o.row.is_some())
        .collect::<Vec<_>>();
    assert_eq!(rows.len(), 2);
    let mut values = vec![];
    for o in rows {
        assert!(o.parameters.is_empty());
        assert_eq!(
            o.bindings
                .iter()
                .map(|b| b.name.as_str())
                .collect::<Vec<_>>(),
            ["c", "b"]
        );
        values.push(g.scalar(o.bindings[1].value).unwrap().wire().canonical());
    }
    values.sort();
    assert_eq!(values, ["false", "true"]);
    assert_eq!(d.coordinates.len(), 2);
    replay(&e, &g.nodes, &g.contexts).unwrap();
    let definition=DEFINITION.replace("\"declarations\":[",r#""declarations":[{"kind":"entity","name":"Finite.Empty","meaning":"空の型域。","parameters":[],"fields":[],"alignments":[]},"#);
    let e = evaluate_observed_bytes(
        custom_sources(
            &definition,
            MAP,
            "law required empty(c:Part,x:(Empty,Bool)):c.quantity=0;",
        ),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &quiet()).unwrap();
    assert!(d.coordinates.is_empty());
    assert_eq!(d.originals.len(), 1);
    assert_eq!(d.originals[0].row, None);
    assert_eq!(
        d.originals[0].parameters,
        [(
            "x".into(),
            Type::Tuple(vec![Type::Ref("Finite.Empty".into()), Type::Bool])
        )]
    );
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn missing_outside_false_guard_and_unsupported_keep_original_sources_without_fabricated_evaluation()
{
    let body = "law required off(c:Part) when false:c.quantity=1;law required unsupported(c:Part):c.quantity>0;";
    let e = example(true, body);
    let mut g = graph(&e);
    let b = architecture(&g, "b");
    let d = retain(&mut g, e.prepared.shared_inputs(), b, 0, &quiet()).unwrap();
    for q in &d.coordinates {
        let o = d
            .originals
            .iter()
            .find(|o| o.reference == q.instance)
            .unwrap();
        assert_eq!(
            g.scalar(o.bindings[0].value).unwrap(),
            &Scalar::Subject {
                snapshot: "v".into(),
                subject: "q".into(),
                entity: "Finite.Part".into()
            }
        );
        assert!(matches!(
            source_text(&e, &g, o.body).as_str(),
            "c.quantity=1" | "c.quantity>0"
        ));
        if let Some(guard) = o.guard {
            assert_eq!(source_text(&e, &g, guard), "false");
        }
        assert!(q.epsilon.is_none());
        assert!(d.evaluations.iter().all(Option::is_none));
        assert!(matches!(data(&g, q.lhs).part(), Part::Source { .. }));
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
    let e = two_owned_example(BODY);
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let objects = crate::observed::object_component_diagram::retain(
        &mut g,
        e.prepared.shared_inputs(),
        a,
        &quiet(),
    )
    .unwrap()
    .unwrap();
    let owned = *objects.architectures.last().unwrap();
    let d = retain(
        &mut g,
        e.prepared.shared_inputs(),
        owned,
        objects.architectures.len() - 1,
        &quiet(),
    )
    .unwrap();
    assert!(
        d.coordinates
            .iter()
            .any(|q| q.guard == EquationGuard::OutsideObject)
    );
    for q in &d.coordinates {
        assert!(d.originals.iter().any(|o| o.reference == q.instance));
        if q.guard == EquationGuard::OutsideObject {
            assert!(q.epsilon.is_none());
            assert!(
                terms(&g, q.nu.unwrap())
                    .iter()
                    .any(|(_, powers)| powers.iter().any(|p| *p == 1))
            );
            assert!(terms(&g, q.residual.unwrap()).is_empty());
            assert_eq!(source_text(&e, &g, q.lhs), "c.quantity");
        }
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn unbounded_parameter_keeps_symbolic_law_typed_sides_and_explicit_unavailable_without_values() {
    let e = example(false, "law required parameter(c:Part,k:Z):c.quantity=k;");
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &quiet()).unwrap();
    assert_eq!(d.status, EquationPresentationStatus::Undetermined);
    let reason = d.unavailable.as_ref().unwrap();
    assert_eq!(reason.declaration, "Chosen.parameter");
    assert_eq!(reason.feature, "値parameterの全域計算が未実装");
    assert!(
        d.rings.is_empty()
            && d.domains.is_empty()
            && d.coordinates.is_empty()
            && d.required.is_empty()
            && d.evaluations.is_empty()
    );
    assert_eq!(d.originals.len(), 1);
    let original = &d.originals[0];
    assert_eq!(original.row, None);
    assert_eq!(original.parameters, [("k".into(), Type::Z)]);
    assert_eq!(source_text(&e, &g, original.body), "c.quantity=k");
    let (left, right) = original.operands.as_ref().unwrap();
    assert_eq!(source_text(&e, &g, left.0), "c.quantity");
    assert_eq!(source_text(&e, &g, right.0), "k");
    assert_eq!((&left.1, &right.1), (&Type::Z, &Type::Z));
    for r in [left.0, right.0] {
        let Part::Source { parameters, .. } = data(&g, r).part() else {
            panic!("source")
        };
        assert_eq!(parameters, &vec![("k".into(), Type::Z)]);
    }
    let source = data(&g, original.reference).source.clone();
    assert!(source.core.is_none());
    for mode in 0..5 {
        let mut bad = (*source).clone();
        match mode {
            0 => bad.outputs.unavailable = None,
            1 => bad.outputs.unavailable.as_mut().unwrap().declaration = "Chosen.other".into(),
            2 => bad.outputs.status = EquationPresentationStatus::Ready,
            3 => bad.outputs.status = EquationPresentationStatus::UnsupportedAlgorithm,
            _ => bad.outputs.originals[0].parameters.clear(),
        }
        assert!(
            bad.recheck(e.prepared.inputs(), &source.architecture, &quiet())
                .is_err()
        );
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn compound_parameter_domain_keeps_external_snapshot_support_scope_and_rejects_omissions() {
    let map=format!(r#"{},{{"id":"w","origin":"external","subjects":[{{"id":"z","type":"Finite.Root","origin":"external"}}],"atoms":[]}}]}}"#,MAP.strip_suffix("]}").unwrap()).replace(r#""origins":["#,r#""origins":[{"id":"external","mode":"proposed","method":"独立の外部参照。","locations":[],"note":"型付きparameter域。"},"#);
    let e = evaluate_observed_bytes(
        custom_sources(
            DEFINITION,
            &map,
            "law required parameter(c:Part,x:(Root,Bool)):c.quantity=0;",
        ),
        &["m=map(Finite.Migration,on=@v/m,reading=Chosen)"],
        &quiet(),
    )
    .unwrap();
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &quiet()).unwrap();
    assert!(d.unavailable.is_none());
    let mut external = 0;
    for original in &d.originals {
        let Some(binding) = original.bindings.iter().find(|b| b.name == "x") else {
            continue;
        };
        let Scalar::Tuple(items) = g.scalar(binding.value).unwrap() else {
            panic!("tuple")
        };
        if matches!(&items[0],Scalar::Subject{snapshot,subject,..}if snapshot=="w"&&subject=="z") {
            external += 1;
            for r in [binding.value, original.body, original.reference] {
                let node = &g.nodes[r.0];
                assert!(node.support.iter().any(|f| f.snapshot == "w"
                    && f.subject == "z"
                    && f.field.is_none()
                    && f.atom.is_none()));
                assert!(node.scope.snapshots.contains("w"));
                assert!(node.scope.modes.contains("proposed"));
                assert!(node.scope.modes.contains("specification"));
            }
        }
    }
    assert_eq!(external, 2);
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
#[test]
fn source_only_unavailable_path_preserves_four_stops_without_returning_incomplete_diagram() {
    let e = example(false, "law required parameter(c:Part,k:Z):c.quantity=k;");
    let mut complete = graph(&e);
    let a = architecture(&complete, "a");
    let before = complete.nodes.len();
    let seen = std::rc::Rc::new(std::cell::Cell::new(0));
    let count = seen.clone();
    let c = Control::new(move |p| {
        if p == Checkpoint::EquationPresentation {
            count.set(count.get() + 1);
        }
        None
    });
    retain(&mut complete, e.prepared.shared_inputs(), a, 0, &c).unwrap();
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
                        &stopping(signal, at)
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
fn symbolic_parameter_scope_keeps_forall_name_type_source_span_and_bound_rows_do_not_requantify() {
    for (body, name, ty) in [
        (
            "law required parameter(c:Part,k:Z):let x=c.quantity in x=k;",
            "k",
            Type::Z,
        ),
        (
            "law required parameter(c:Part,b:Bool):c.quantity=(if b then 0 else 1);",
            "b",
            Type::Bool,
        ),
    ] {
        let e = example(false, body);
        let mut g = graph(&e);
        let a = architecture(&g, "a");
        let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &quiet()).unwrap();
        let original = d.originals.iter().find(|o| o.row.is_none()).unwrap();
        let (left, right) = original.operands.as_ref().unwrap();
        let source = std::str::from_utf8(e.prepared.inputs().sources().law().bytes()).unwrap();
        let binder = format!("{name}:{}", if name == "k" { "Z" } else { "Bool" });
        let at = source.find(&binder).unwrap();
        for r in [original.reference, original.body, left.0, right.0] {
            let qs = &g.nodes[r.0].scope.quantifiers;
            assert_eq!(qs.len(), 1);
            let q = &qs[0];
            assert_eq!(q.kind, crate::law::ast::QuantKind::Forall);
            assert_eq!(q.name, name);
            assert_eq!(q.ty, ty);
            assert_eq!(q.occurrence, (at, at + name.len()));
            assert!(q.domain.is_none() && q.context.is_none());
        }
        for row in d.originals.iter().filter(|o| o.row.is_some()) {
            let (left, right) = row.operands.as_ref().unwrap();
            for r in [row.reference, row.body, left.0, right.0] {
                assert!(g.nodes[r.0].scope.quantifiers.is_empty());
            }
        }
        replay(&e, &g.nodes, &g.contexts).unwrap();
    }
}
#[test]
fn symbolic_quantifier_removal_name_type_kind_span_domain_and_native_scope_changes_are_rejected() {
    let e = example(false, "law required parameter(c:Part,k:Z):c.quantity=k;");
    let mut g = graph(&e);
    let a = architecture(&g, "a");
    let d = retain(&mut g, e.prepared.shared_inputs(), a, 0, &quiet()).unwrap();
    let original = &d.originals[0];
    let source = data(&g, original.reference).source.clone();
    let body = original.body.0 - source.base;
    for mode in 0..8 {
        let mut bad = (*source).clone();
        if mode == 7 {
            bad.outputs.originals[0].quantifiers.clear();
        } else {
            let Part::Source { quantifiers, .. } = &mut bad.parts[body] else {
                panic!("source")
            };
            match mode {
                0 => quantifiers.clear(),
                1 => quantifiers[0].kind = crate::law::ast::QuantKind::Exists,
                2 => quantifiers[0].name = "other".into(),
                3 => quantifiers[0].ty = Type::Q,
                4 => quantifiers[0].occurrence = (0, 1),
                5 => quantifiers[0].domain = Some(NodeRef(0)),
                _ => quantifiers[0].context = Some(g.contexts[original.body.0]),
            }
        }
        assert!(
            bad.recheck(e.prepared.inputs(), &source.architecture, &quiet())
                .is_err(),
            "mode {mode}"
        );
    }
    for r in [original.body, original.reference] {
        let mut nodes = g.nodes.clone();
        nodes[r.0].scope.quantifiers.clear();
        assert!(replay(&e, &nodes, &g.contexts).is_err());
    }
    replay(&e, &g.nodes, &g.contexts).unwrap();
}
