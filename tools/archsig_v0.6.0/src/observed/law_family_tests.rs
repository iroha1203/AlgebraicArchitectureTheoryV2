use super::*;
use crate::{
    control::{Limits, Usage},
    observed::{PreparedObserved, request::resolve_native_for_test},
};
#[allow(dead_code)]
mod fixture {
    include!("../../tests/common/polynomial_law_family_data.rs");
    pub fn empty(body: &str) -> Arc<CheckedInputs> {
        let base = inputs(false, false, "law required seed(c:Part):c.quantity=0;");
        let source = String::from_utf8(base.sources().definitions()[0].bytes().to_vec()).unwrap();
        let source=source.replace("\"declarations\":[",r#""declarations":[{"kind":"entity","name":"Family.Empty","meaning":"空の型。","parameters":[],"fields":[],"alignments":[]},"#);
        let defs =
            archsig::definition::check_definitions(&[("definition0", source.as_bytes())]).unwrap();
        let digest = &defs.vocabularies["Family"].digest;
        let law = format!(
            "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Family version \"1\" digest \"{digest}\";{body}}}"
        );
        Arc::new(
            check_inputs(
                InputSources::from_bytes(
                    vec![source.into_bytes()],
                    law.into_bytes(),
                    MAP.replace("@DIGEST@", digest).into_bytes(),
                ),
                &mut Control::new(Limits::default(), |_| Usage::default()),
            )
            .unwrap(),
        )
    }
}
#[allow(dead_code)]
mod finite_fixture {
    include!("../../tests/common/finite_law_reading_data.rs");
}
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn prepared(inputs: Arc<crate::input::CheckedInputs>) -> PreparedObserved {
    let requests = resolve_native_for_test(
        inputs.law(),
        inputs.archmap(),
        &["b=build(Selected,on=@v/root)"],
        &mut quiet(),
    )
    .unwrap();
    PreparedObserved {
        inputs,
        requests,
        object: None,
    }
}
fn start(p: &PreparedObserved) -> (Graph, NodeRef, Vec<NodeRef>) {
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
    let objects = crate::observed::object_component_diagram::retain(
        &mut g,
        p.shared_inputs(),
        a.reference,
        &mut quiet(),
    )
    .unwrap()
    .unwrap();
    (g, a.reference, objects.architectures)
}
fn replay(p: &PreparedObserved, source: &Graph) -> Result<(), ValidationFailure> {
    let env = Environment::with_prepared(p, &mut quiet())?;
    let mut g = Graph::new(&quiet());
    g.requests = source.requests.clone();
    g.frames = source.frames.clone();
    g.instances = source.instances.clone();
    g.iterations = source.iterations.clone();
    g.cases = source.cases.clone();
    g.universal_witnesses = source.universal_witnesses.clone();
    g.checked_answers = source.checked_answers.clone();
    for (i, n) in source.nodes.iter().enumerate() {
        g.active = source.contexts[i];
        env.validate(&g, n)?;
        g.push(n.clone())?;
    }
    Ok(())
}
fn copy_graph(g: &Graph, c: &Control) -> Graph {
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
fn poly(
    p: &PreparedObserved,
) -> (
    Graph,
    Vec<NodeRef>,
    Vec<crate::observed::polynomial_law_diagram::Diagram>,
) {
    let (mut g, a, objects) = start(p);
    let ds = crate::observed::polynomial_law_diagram::retain_family(
        &mut g,
        p.shared_inputs(),
        a,
        &mut quiet(),
    )
    .unwrap();
    (g, objects, ds)
}
fn family_data(g: &Graph, r: NodeRef) -> &Data {
    let Some(Payload::Construction(v)) = &g.nodes[r.0].payload else {
        panic!()
    };
    let D::LawFamily(d) = &v.data else { panic!() };
    d
}
fn assert_exhaustion_wire(g: &Graph, proof: NodeRef, domain: NodeRef, rows: &[Row]) {
    // 独立した公開形式の期待値を、実際のNode出力まで照合する。
    let expected = Json::obj([
        ("kind", Json::str("finite_exhaustion")),
        (
            "data",
            Json::obj([
                ("domain", domain.wire()),
                ("checked", Json::Nat(rows.len() as u64)),
                (
                    "instances",
                    ref_array(&rows.iter().map(|r| r.evaluation).collect::<Vec<_>>()),
                ),
            ]),
        ),
    ]);
    assert_eq!(family_data(g, proof).wire, expected);
    let node = g.get(proof).unwrap();
    assert_eq!(node.ty, NodeType::Evidence);
    let Json::Obj(ref wire) = node.wire(proof.0, &g.nodes[..proof.0]) else {
        panic!()
    };
    assert_eq!(wire["type"], Json::str("Evidence"));
    assert_eq!(wire["value"], expected);
}
fn assert_upstream(p: &PreparedObserved) {
    let upstream = crate::observed::object_law_compatibility::object_law_compatibility(
        p.shared_inputs(),
        "Selected",
        "v",
        "root",
        &mut quiet(),
    )
    .unwrap_or_else(|failure| {
        let issues = failure.active().and_then(|active| match active.outcome() {
            crate::observed::object_evaluate::ObjectEvaluationOutcome::Evaluated(e) => {
                let wire = e.wire();
                let Json::Obj(fields) = &wire else {
                    return None;
                };
                fields.get("issues").cloned()
            }
            _ => None,
        });
        panic!(
            "元Lawの全対象評価が未完成: {:?}; {:?}",
            failure.cause(),
            issues
        )
    });
    assert!(!upstream.evaluations().is_empty());
}
#[test]
fn finite_boolean_family_uses_real_rows_every_object_and_full_exhaustion() {
    let p = prepared(fixture::inputs(
        false,
        false,
        "law optional bit(c:Part,b:Bool) when b:c.quantity=0;",
    ));
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let (mut g, objects, ds) = poly(&p);
    let mut seen = vec![];
    for (object, diagram) in ds.iter().enumerate() {
        for t in diagram.originals.iter().filter(|o| o.row.is_none()) {
            let answer = check(&env, &mut g, t.reference, objects[object], &mut quiet())
                .unwrap()
                .unwrap();
            let who = match g.scalar(t.bindings[0].value).unwrap() {
                Scalar::Subject { subject, .. } => subject.clone(),
                _ => panic!(),
            };
            let outside =
                object != 0 && ((object == 1 && who == "q") || (object == 2 && who == "p"));
            let established = outside || who == "p";
            assert_eq!(
                answer.status,
                if established {
                    Decision::Established
                } else {
                    Decision::Refuted
                }
            );
            let eval = answer.outputs["evaluation"];
            let d = family_data(&g, eval);
            let Kind::Evaluation {
                domain,
                rows,
                value,
            } = &d.kind
            else {
                panic!()
            };
            assert_eq!(rows.len(), 2);
            assert_eq!(g.boolean(*value).unwrap(), Some(established));
            let Json::Obj(wire) = &d.wire else { panic!() };
            assert_eq!(
                wire["expression"],
                frames::origin(&g, t.reference)
                    .unwrap()
                    .unwrap()
                    .body_reference
                    .wire()
            );
            assert_eq!(wire["environment"], objects[object].wire());
            assert_eq!(wire["applicability"], Json::str("applicable"));
            let Json::Obj(proposition) = &family_data(&g, answer.claim.unwrap()).wire else {
                panic!()
            };
            assert_eq!(proposition["predicate"], Json::str("law_holds"));
            assert_eq!(proposition["operands"], Json::Arr(vec![t.reference.wire()]));
            assert_eq!(
                proposition["quantifiers"],
                Json::Arr(d.scope.quantifiers.iter().map(Quantifier::wire).collect())
            );
            if !established {
                assert!(answer.evidence.iter().any(|r|matches!(&g.get(*r).unwrap().payload,Some(Payload::Counterexample{bindings,..}) if bindings.len()==2 && bindings.iter().any(|b|b.name=="c" && matches!(g.scalar(b.value).unwrap(),Scalar::Subject{subject,..} if subject==&who)) && bindings.iter().any(|b|b.name=="b" && g.scalar(b.value).unwrap()==&Scalar::Bool(true)))));
            }
            let members = match &family_data(&g, *domain).kind {
                Kind::Domain { members } => members,
                _ => panic!(),
            };
            assert_eq!(members.len(), 2);
            for (index, row) in rows.iter().enumerate() {
                let origin = frames::origin(&g, row.law).unwrap().unwrap();
                assert_eq!(origin.object, object);
                assert_eq!(
                    g.scalar(origin.bindings[1].value).unwrap(),
                    &Scalar::Bool(index == 1)
                );
                assert_eq!(origin.outside, outside);
            }
            let claim = answer.claim.unwrap();
            assert_eq!(
                family_data(&g, claim).judgment.as_ref().unwrap().status,
                answer.status
            );
            if established {
                let proof = family_data(&g, *answer.evidence.last().unwrap());
                assert!(matches!(proof.kind,Kind::Exhaustion{evaluation} if evaluation==eval));
                assert_exhaustion_wire(&g, *answer.evidence.last().unwrap(), *domain, rows);
            }
            assert!(d.scope.assignments);
            assert!(
                d.scope
                    .quantifiers
                    .iter()
                    .any(|q| q.name == "b" && q.domain.is_some())
            );
            seen.push((object, who, answer.status));
        }
    }
    assert_eq!(seen.len(), 6);
    replay(&p, &g).unwrap();
}
#[test]
fn finite_product_family_keeps_every_parameter_type_domain_and_binding_order() {
    let p = prepared(fixture::inputs(
        false,
        false,
        "law required grid(c:Part,b:Bool,n:Fp(2)):c.quantity=0;",
    ));
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let (mut g, objects, ds) = poly(&p);
    let t = ds[0].originals.iter().find(|o| o.row.is_none()).unwrap();
    let answer = check(&env, &mut g, t.reference, objects[0], &mut quiet())
        .unwrap()
        .unwrap();
    let d = family_data(&g, answer.outputs["evaluation"]);
    assert_eq!(d.parameters.len(), 2);
    let Kind::Evaluation { domain, rows, .. } = &d.kind else {
        panic!()
    };
    assert_eq!(rows.len(), 4);
    let Kind::Domain { members } = &family_data(&g, *domain).kind else {
        panic!()
    };
    assert_eq!(members.len(), 4);
    for (i, r) in members.iter().enumerate() {
        let Kind::Member {
            values,
            scalar,
            wire,
            ..
        } = &family_data(&g, *r).kind
        else {
            panic!()
        };
        assert_eq!(values.len(), 2);
        assert_eq!(
            scalar.ty(),
            Type::Tuple(vec![Type::Bool, Type::Fp("2".into())])
        );
        assert_eq!(wire, &scalar.wire());
        assert_eq!(g.scalar(values[0]).unwrap(), &Scalar::Bool(i >= 2));
    }
    replay(&p, &g).unwrap();
}
#[test]
fn missing_body_is_undetermined_inside_and_conditional_true_outside() {
    let p = prepared(fixture::inputs(
        true,
        false,
        "law required bit(c:Part,b:Bool):c.quantity=0;",
    ));
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let (mut g, objects, ds) = poly(&p);
    let mut statuses = vec![];
    for (object, d) in ds.iter().enumerate() {
        let t=d.originals.iter().find(|o|o.row.is_none()&&matches!(g.scalar(o.bindings[0].value).unwrap(),Scalar::Subject{subject,..} if subject=="q")).unwrap();
        let answer = check(&env, &mut g, t.reference, objects[object], &mut quiet())
            .unwrap()
            .unwrap();
        statuses.push(answer.status);
        if object == 1 {
            assert!(answer.reasons.is_empty())
        } else {
            assert!(!answer.reasons.is_empty())
        }
    }
    assert_eq!(
        statuses,
        vec![
            Decision::Undetermined,
            Decision::Established,
            Decision::Undetermined
        ]
    );
    replay(&p, &g).unwrap();
}

#[test]
fn empty_parameter_product_has_zero_real_rows_and_does_not_evaluate_body() {
    let p = prepared(fixture::empty(
        "law required empty(c:Part,e:(Empty,Bool)):c.quantity=1;",
    ));
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let (mut g, objects, ds) = poly(&p);
    let mut count = 0;
    for (object, d) in ds.iter().enumerate() {
        for t in d.originals.iter().filter(|o| o.row.is_none()) {
            let before = g.nodes.len();
            let a = check(&env, &mut g, t.reference, objects[object], &mut quiet())
                .unwrap()
                .unwrap();
            assert_eq!(a.status, Decision::Established);
            let e = family_data(&g, a.outputs["evaluation"]);
            let Kind::Evaluation {
                rows,
                value,
                domain,
            } = &e.kind
            else {
                panic!()
            };
            assert!(rows.is_empty());
            assert_eq!(g.boolean(*value).unwrap(), Some(true));
            assert!(
                matches!(&family_data(&g,*domain).kind,Kind::Domain{members} if members.is_empty())
            );
            assert_exhaustion_wire(&g, *a.evidence.last().unwrap(), *domain, rows);
            assert!(
                g.nodes[before..]
                    .iter()
                    .all(|n| matches!(n.payload, Some(Payload::Construction(_))))
            );
            count += 1;
        }
    }
    assert_eq!(count, 6);
    replay(&p, &g).unwrap();
}
#[test]
fn finite_composite_parameter_values_remain_complete_and_typed() {
    for parameter in ["x:(Bool,Bool)", "s:Set<Bool>", "o:Option<Bool>"] {
        let p = prepared(fixture::inputs(
            false,
            false,
            &format!("law optional composite(c:Part,{parameter}):c.quantity=0;"),
        ));
        let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
        let (mut g, objects, ds) = poly(&p);
        let expected = if parameter.starts_with("o:") { 3 } else { 4 };
        for (object, d) in ds.iter().enumerate() {
            for t in d.originals.iter().filter(|o| o.row.is_none()) {
                let a = check(&env, &mut g, t.reference, objects[object], &mut quiet())
                    .unwrap()
                    .unwrap();
                let data = family_data(&g, a.outputs["evaluation"]);
                let Kind::Evaluation { domain, rows, .. } = &data.kind else {
                    panic!()
                };
                assert_eq!(rows.len(), expected);
                let Kind::Domain { members } = &family_data(&g, *domain).kind else {
                    panic!()
                };
                assert_eq!(members.len(), expected);
                for (r, row) in members.iter().zip(rows) {
                    let member = family_data(&g, *r);
                    let binding = frames::origin(&g, row.law).unwrap().unwrap().bindings[1].value;
                    assert_eq!(member.scalar().unwrap(), g.scalar(binding).unwrap());
                    assert_eq!(member.wire(), member.scalar().unwrap().wire());
                }
            }
        }
        replay(&p, &g).unwrap();
    }
}
#[test]
fn all_false_guards_keep_unbounded_body_unread_and_count_every_row() {
    let p = prepared(fixture::inputs(
        true,
        false,
        "law required skipped(c:Part,b:Bool) when false:forall k:Z.k=0;",
    ));
    assert_upstream(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let (mut g, objects, ds) = poly(&p);
    for (object, d) in ds.iter().enumerate() {
        for t in d.originals.iter().filter(|o| o.row.is_none()) {
            let a = check(&env, &mut g, t.reference, objects[object], &mut quiet())
                .unwrap()
                .unwrap();
            assert_eq!(a.status, Decision::Established);
            let eval = family_data(&g, a.outputs["evaluation"]);
            let Kind::Evaluation { domain, rows, .. } = &eval.kind else {
                panic!()
            };
            assert_eq!(rows.len(), 2);
            for row in rows {
                if let Some(Payload::Evaluation { parts, .. }) = &g.nodes[row.evaluation.0].payload
                {
                    let body = parts.last().unwrap();
                    assert!(body.value.is_none());
                    assert!(body.children.is_empty());
                }
            }
            assert_exhaustion_wire(&g, *a.evidence.last().unwrap(), *domain, rows);
        }
    }
    replay(&p, &g).unwrap();
}
fn sample() -> (PreparedObserved, Graph, Vec<NodeRef>, NodeRef, Answer) {
    let p = prepared(fixture::inputs(
        false,
        false,
        "law required bit(c:Part,b:Bool):c.quantity=0;",
    ));
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let (mut g, objects, ds) = poly(&p);
    let t = ds[0]
        .originals
        .iter()
        .find(|o| o.row.is_none())
        .unwrap()
        .reference;
    let a = check(&env, &mut g, t, objects[0], &mut quiet())
        .unwrap()
        .unwrap();
    (p, g, objects, t, a)
}
fn edit(g: &mut Graph, r: NodeRef, f: impl FnOnce(&mut Data)) {
    let Some(Payload::Construction(v)) = &mut g.nodes[r.0].payload else {
        panic!()
    };
    let D::LawFamily(d) = &mut v.data else {
        panic!()
    };
    f(d);
    let d = d.clone();
    let n = &mut g.nodes[r.0];
    n.ty = d.ty();
    n.arguments = d.arguments();
    n.support = d.support;
    n.scope = d.scope;
    n.reasons = d.reasons;
    n.evidence = d.evidence;
    n.judgment = d.judgment;
}
#[test]
fn whole_family_rejects_coverage_order_environment_wire_scope_and_judgment_forgery() {
    let (p, g, objects, _, a) = sample();
    let e = a.outputs["evaluation"];
    let q = a.claim.unwrap();
    let proof = *a.evidence.last().unwrap();
    let Kind::Evaluation { domain, rows, .. } = family_data(&g, e).kind.clone() else {
        panic!()
    };
    let domain_ref = domain;
    let Kind::Domain { members } = family_data(&g, domain).kind.clone() else {
        panic!()
    };
    for mode in 0..19 {
        let mut bad = copy_graph(&g, &quiet());
        let r = match mode {
            11 => q,
            12 | 18 => proof,
            13 | 14 => domain_ref,
            15 | 16 => members[0],
            _ => e,
        };
        edit(&mut bad, r, |d| match mode {
            0 => {
                let Kind::Evaluation { rows, .. } = &mut d.kind else {
                    panic!()
                };
                rows.pop();
            }
            1 => {
                let Kind::Evaluation { rows, .. } = &mut d.kind else {
                    panic!()
                };
                rows[1] = rows[0].clone();
            }
            2 => {
                let Kind::Evaluation { rows, .. } = &mut d.kind else {
                    panic!()
                };
                rows.reverse();
            }
            3 => {
                let Kind::Evaluation { rows, .. } = &mut d.kind else {
                    panic!()
                };
                rows[0].evaluation = rows[1].evaluation;
                rows[0].proposition = rows[1].proposition;
            }
            4 => {
                let Kind::Evaluation { domain, .. } = &mut d.kind else {
                    panic!()
                };
                *domain = members[0];
            }
            5 => {
                let Kind::Evaluation { value, .. } = &mut d.kind else {
                    panic!()
                };
                *value = None;
            }
            6 => {
                let Json::Obj(w) = &mut d.wire else { panic!() };
                w.insert("applicability".into(), Json::str("not_applicable"));
            }
            7 => d.support.clear(),
            8 => d.scope.assignments = false,
            9 => d.scope.quantifiers.clear(),
            10 => d.scope.snapshots.clear(),
            11 => {
                d.judgment.as_mut().unwrap().status = Decision::Refuted;
            }
            12 => {
                let Json::Obj(w) = &mut d.wire else { panic!() };
                let Some(Json::Obj(data)) = w.get_mut("data") else {
                    panic!()
                };
                data.insert("checked".into(), Json::Nat(1));
            }
            13 => {
                let Kind::Domain { members } = &mut d.kind else {
                    panic!()
                };
                members.reverse();
            }
            14 => {
                let Kind::Domain { members } = &mut d.kind else {
                    panic!()
                };
                members.pop();
            }
            15 => {
                let Kind::Member { values, .. } = &mut d.kind else {
                    panic!()
                };
                values[0] = frames::origin(&g, rows[1].law).unwrap().unwrap().bindings[1].value;
            }
            16 => {
                let Kind::Member { scalar, wire, .. } = &mut d.kind else {
                    panic!()
                };
                *scalar = Scalar::Bool(true);
                *wire = Json::Bool(true);
                d.wire = Json::Bool(true);
            }
            17 => d.architecture = objects[1],
            18 => {
                let Json::Obj(w) = &mut d.wire else { panic!() };
                let Some(Json::Obj(ref data)) = w.remove("data") else {
                    panic!()
                };
                w.extend(data.clone());
            }
            _ => unreachable!(),
        });
        assert!(replay(&p, &bad).is_err(), "mode {mode}");
    }
    let other = prepared(fixture::inputs(
        false,
        false,
        "law required bit(c:Part,b:Bool):c.quantity=1;",
    ));
    assert!(replay(&other, &g).is_err());
    replay(&p, &g).unwrap();
}
#[test]
fn whole_family_self_and_future_refs_fail_before_recursive_validation() {
    let (p, g, _, _, a) = sample();
    let e = a.outputs["evaluation"];
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    for mode in 0..8 {
        let mut bad = copy_graph(&g, &quiet());
        let invalid = NodeRef(e.0 + usize::from(mode >= 4));
        edit(&mut bad, e, |d| match mode % 4 {
            0 => d.template = invalid,
            1 => d.architecture = invalid,
            2 => {
                let Kind::Evaluation { domain, .. } = &mut d.kind else {
                    panic!()
                };
                *domain = invalid;
            }
            _ => {
                let Kind::Evaluation { rows, .. } = &mut d.kind else {
                    panic!()
                };
                rows[0].evaluation = invalid;
            }
        });
        assert!(
            matches!(
                env.recheck_node(&bad, &bad.nodes[e.0], e.0),
                Err(ValidationFailure::Internal(_))
            ),
            "mode {mode}"
        );
    }
}
#[test]
fn unbounded_parameter_is_retained_without_a_finite_family_claim() {
    let p = prepared(fixture::inputs(
        false,
        false,
        "law required unbounded(c:Part,k:Z):c.quantity=k;",
    ));
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let (mut g, objects, ds) = poly(&p);
    for (object, d) in ds.iter().enumerate() {
        assert!(d.unavailable.is_none());
        assert!(!d.coordinates.is_empty());
        for coordinate in &d.coordinates {
            assert!(coordinate.row.is_none());
            let Some(Payload::Construction(value)) = &g.nodes[coordinate.nu.unwrap().0].payload
            else {
                panic!("numeric polynomial")
            };
            let D::PolynomialLaw(data) = &value.data else {
                panic!("polynomial source")
            };
            let Json::Obj(ref polynomial) = data.wire() else {
                panic!("polynomial")
            };
            assert_eq!(
                polynomial.get("parameters"),
                Some(&Json::Arr(vec![Json::obj([
                    ("name", Json::str("k")),
                    ("type", Type::Z.wire())
                ])]))
            );
        }
        for t in d.originals.iter().filter(|o| o.row.is_none()) {
            let before = g.nodes.len();
            assert!(
                check(&env, &mut g, t.reference, objects[object], &mut quiet())
                    .unwrap()
                    .is_none()
            );
            assert_eq!(before, g.nodes.len());
        }
    }
    replay(&p, &g).unwrap();
}
#[test]
fn whole_family_four_stops_keep_completed_prefix_and_restore_request_context() {
    use std::{cell::Cell, rc::Rc};
    let p = prepared(fixture::inputs(
        false,
        false,
        "law required bit(c:Part,b:Bool):c.quantity=0;",
    ));
    let (initial, objects, ds) = poly(&p);
    let template=ds[1].originals.iter().find(|o|o.row.is_none()&&matches!(initial.scalar(o.bindings[0].value).unwrap(),Scalar::Subject{subject,..} if subject=="q")).unwrap().reference;
    let seen = Rc::new(Cell::new(0));
    let count = seen.clone();
    let mut c = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::ObjectEvaluation {
            count.set(count.get() + 1)
        }
        Usage::default()
    });
    let mut full = copy_graph(&initial, &c);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    check(&env, &mut full, template, objects[1], &mut c)
        .unwrap()
        .unwrap();
    let total = seen.get();
    assert!(total > 5);
    let mut final_retained = false;
    for mode in 0..4 {
        for at in 1..=total {
            let seen = Rc::new(Cell::new(0));
            let count = seen.clone();
            let mut c = Control::new(
                Limits {
                    time_ms: (mode == 0).then_some(1),
                    memory_mib: (mode == 1).then_some(1),
                },
                move |point| {
                    if point == Checkpoint::ObjectEvaluation {
                        count.set(count.get() + 1)
                    }
                    let stop = count.get() >= at;
                    Usage {
                        elapsed_ms: u128::from(stop && mode == 0),
                        memory_mib: u128::from(stop && mode == 1),
                        signal: (stop && mode >= 2).then_some(if mode == 2 {
                            crate::result::Signal::Int
                        } else {
                            crate::result::Signal::Term
                        }),
                    }
                },
            );
            let mut g = copy_graph(&initial, &c);
            let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
            assert!(matches!(
                check(&env, &mut g, template, objects[1], &mut c),
                Err(ValidationFailure::Stop(_))
            ));
            assert_eq!(g.active, initial.active);
            assert!(env.architecture_ref().is_none());
            assert_eq!(g.nodes, &full.nodes[..g.nodes.len()]);
            assert_eq!(g.contexts, &full.contexts[..g.nodes.len()]);
            final_retained |= g.nodes.len() == full.nodes.len();
            replay(&p, &g).unwrap();
        }
    }
    assert!(final_retained);
}

#[test]
fn true_and_missing_guards_keep_quantified_body_judgment_and_missing_reasons() {
    for missing in [false, true] {
        let p = prepared(fixture::inputs(
            missing,
            false,
            "law required quantified(c:Part,b:Bool) when c.quantity=0:forall k:Z.k=0;",
        ));
        assert_upstream(&p);
        let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
        let (mut g, objects, ds) = poly(&p);
        for (object, d) in ds.iter().enumerate() {
            for t in d.originals.iter().filter(|o| o.row.is_none()) {
                let Scalar::Subject { subject, .. } = g.scalar(t.bindings[0].value).unwrap() else {
                    panic!()
                };
                let subject = subject.clone();
                let outside = object != 0
                    && ((object == 1 && subject == "q") || (object == 2 && subject == "p"));
                let expected = if outside || (!missing && subject == "q") {
                    Decision::Established
                } else if subject == "p" {
                    Decision::Refuted
                } else {
                    Decision::Undetermined
                };
                let a = check(&env, &mut g, t.reference, objects[object], &mut quiet())
                    .unwrap()
                    .unwrap();
                assert_eq!(
                    a.status, expected,
                    "object {object} subject {subject} missing {missing}"
                );
                if expected == Decision::Undetermined {
                    assert!(!a.reasons.is_empty());
                }
                let Kind::Evaluation { rows, .. } = &family_data(&g, a.outputs["evaluation"]).kind
                else {
                    panic!()
                };
                assert_eq!(rows.len(), 2);
                if expected == Decision::Refuted {
                    for row in rows {
                        let Payload::Evaluation { parts, .. } =
                            g.get(row.evaluation).unwrap().payload.as_ref().unwrap()
                        else {
                            panic!()
                        };
                        assert!(!parts.last().unwrap().children.is_empty());
                        assert_eq!(g.boolean(parts.last().unwrap().value).unwrap(), Some(false));
                    }
                }
            }
        }
        replay(&p, &g).unwrap();
    }
}
