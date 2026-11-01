use super::*;
use crate::observed::{PreparedObserved, request::resolve_native_for_test};
#[allow(dead_code)]
mod fixture {
    include!("../../../tests/common/polynomial_law_family_data.rs");
}
use crate::control::quiet;
fn prepared(missing: bool, tuple: bool, body: &str, root: &str) -> PreparedObserved {
    let inputs = fixture::inputs(missing, tuple, body);
    let ask = format!("b=build(Selected,on=@v/{root})");
    let requests =
        resolve_native_for_test(inputs.law(), inputs.archmap(), &[ask.as_str()], &quiet()).unwrap();
    PreparedObserved {
        inputs,
        requests,
        object: None,
    }
}
fn built(p: &PreparedObserved) -> (Graph, NodeRef) {
    let c = quiet();
    let env = Environment::with_prepared(p, &c).unwrap();
    let mut g = Graph::new(&c);
    g.requests = p.requests().requests().to_vec();
    let a = crate::observed::architecture_result::build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[0],
        &c,
    )
    .unwrap();
    assert!(a.complete, "{:?}", a.reasons);
    (g, a.reference)
}
fn replay(
    p: &PreparedObserved,
    original: &Graph,
    nodes: &[Node],
) -> Result<Graph, ValidationFailure> {
    let c = quiet();
    let env = Environment::with_prepared(p, &c)?;
    let mut g = Graph::new(&c);
    g.requests = original.requests.clone();
    g.checked_answers = original.checked_answers.clone();
    g.frames = original.frames.clone();
    g.iterations = original.iterations.clone();
    g.instances = original.instances.clone();
    g.cases = original.cases.clone();
    g.universal_witnesses = original.universal_witnesses.clone();
    for (index, node) in nodes.iter().enumerate() {
        g.active = original.contexts[index];
        env.validate(&g, node).map_err(|e| {
            ValidationFailure::Internal(format!(
                "replay env {index} {:?} {:?}: {e:?}",
                node.ty, node.rule
            ))
        })?;
        g.push(node.clone()).map_err(|e| {
            ValidationFailure::Internal(format!(
                "replay graph {index} {:?} {:?}: {e:?}",
                node.ty, node.rule
            ))
        })?;
    }
    Ok(g)
}
fn data(g: &Graph, r: NodeRef) -> &Data {
    let Some(Payload::Construction(v)) = &g.nodes[r.0].payload else {
        panic!("native")
    };
    let D::PolynomialLaw(d) = &v.data else {
        panic!("finite")
    };
    d
}

const BODY: &str = "law required zero(c:Part):c.quantity=0;law optional one(c:Part):c.quantity=1;";
fn boolean(g: &Graph, r: Option<NodeRef>) -> Option<bool> {
    r.map(|r| match g.scalar(r).unwrap() {
        Scalar::Bool(v) => *v,
        _ => panic!("Bool"),
    })
}
fn origin<'a>(g: &'a Graph, r: &reading::Reading) -> (&'a str, &'a [Binding]) {
    match data(g, r.instance).part() {
        Part::LawInstance { name, bindings, .. } => (name, bindings),
        _ => panic!("LawInstance"),
    }
}
fn subject(g: &Graph, bindings: &[Binding]) -> String {
    let b = bindings.iter().find(|b| b.name == "c").unwrap();
    match g.scalar(b.value).unwrap() {
        Scalar::Subject { subject, .. } => subject.clone(),
        _ => panic!("subject"),
    }
}
#[test]
fn original_polynomial_readings_keep_each_object_row_and_independent_body_truth() {
    let p = prepared(false, false, BODY, "root");
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &quiet()).unwrap();
    assert_eq!(ds.len(), 3);
    for (object, d) in ds.iter().enumerate() {
        assert_eq!(d.readings.len(), 4);
        for r in &d.readings {
            let (name, bindings) = origin(&g, r);
            let who = subject(&g, bindings);
            let applies = object == 0 || (object == 1 && who == "p") || (object == 2 && who == "q");
            let truth = (who == "p") == name.ends_with("zero");
            assert_eq!(boolean(&g, r.body), applies.then_some(truth));
            assert_eq!(boolean(&g, r.holds), Some(!applies || truth));
            assert_eq!(r.evaluations.is_empty(), !applies);
            for value in [r.body, r.holds].into_iter().flatten() {
                assert!(g.nodes[value.0].arguments.contains(&r.instance));
                assert!(!g.nodes[value.0].scope.assignments);
            }
        }
    }
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn polynomial_false_guard_does_not_evaluate_missing_body() {
    let p = prepared(
        true,
        false,
        "law required off(c:Part) when false:c.quantity=0;",
        "root",
    );
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &quiet()).unwrap();
    for d in &ds {
        assert_eq!(d.readings.len(), 2);
        for r in &d.readings {
            assert_eq!(boolean(&g, r.body), None);
            assert_eq!(boolean(&g, r.holds), Some(true));
        }
    }
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn polynomial_missing_self_equality_retains_exact_inference_and_unknown_operands_separately() {
    let p = prepared(
        true,
        false,
        "law required same(c:Part):c.quantity=c.quantity;",
        "root",
    );
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &quiet()).unwrap();
    for (object, d) in ds.iter().enumerate() {
        for r in &d.readings {
            let (_, bindings) = origin(&g, r);
            let who = subject(&g, bindings);
            let applies = object == 0 || (object == 1 && who == "p") || (object == 2 && who == "q");
            assert_eq!(boolean(&g, r.body), applies.then_some(true));
            assert_eq!(boolean(&g, r.holds), Some(true));
            if applies && who == "q" {
                // 通常Evaluatorの厳密な同一式判定は保持する。operandを観測済みにしない。
                let source = &data(&g, r.instance).source;
                let core = source.core.as_ref().unwrap();
                let original = core
                    .base()
                    .base()
                    .evaluations()
                    .iter()
                    .find(|e| {
                        e.position().object == object
                            && e.position().instance
                                == d.originals
                                    .iter()
                                    .find(|o| o.reference == r.instance)
                                    .unwrap()
                                    .instance
                    })
                    .unwrap();
                let crate::observed::object_evaluate::ObjectEvaluationOutcome::Evaluated(raw) =
                    original.evaluation().outcome()
                else {
                    panic!("observed graph")
                };
                assert_eq!(r.evaluations.len(), 1);
                let n = &raw.nodes[r.evaluations[0]];
                let Some(Payload::Evaluation {
                    expression,
                    parts,
                    value,
                    ..
                }) = &n.payload
                else {
                    panic!("Evaluation")
                };
                assert!(!matches!(
                    raw.nodes[expression.0].payload,
                    Some(Payload::CompletionSeed { .. })
                ));
                assert!(n.scope.completions && !n.evidence.is_empty());
                assert!(matches!(
                    raw.nodes[value.unwrap().0].payload,
                    Some(Payload::Scalar(Scalar::Bool(true)))
                ));
                assert!(n.reasons.iter().any(|r| r.missing.iter().any(
                    |f| f.subject == "q" && f.field.as_deref() == Some("Family.Part.quantity")
                )));
                assert_eq!(parts[0].children.len(), 2);
                for child in &parts[0].children {
                    assert!(matches!(
                        &raw.nodes[child.0].payload,
                        Some(Payload::Evaluation { value: None, .. })
                    ));
                }
                assert!(g.nodes[r.body.unwrap().0].scope.completions);
            }
        }
    }
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn polynomial_readings_preserve_all_bool_bindings_and_do_not_choose_a_display_row() {
    let p = prepared(
        false,
        false,
        "law required bit(c:Part,b:Bool):(c.quantity=0)=b;",
        "root",
    );
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &quiet()).unwrap();
    for (object, d) in ds.iter().enumerate() {
        let active = if object == 0 { 4 } else { 2 };
        assert_eq!(
            d.readings.iter().filter(|r| r.body.is_some()).count(),
            active
        );
        for r in &d.readings {
            let (_, bindings) = origin(&g, r);
            let who = subject(&g, bindings);
            if let Some(body) = r.body {
                let b = bindings.iter().find(|b| b.name == "b").unwrap();
                let Scalar::Bool(b) = g.scalar(b.value).unwrap() else {
                    panic!("Bool")
                };
                assert_eq!(boolean(&g, Some(body)), Some((who == "p") == *b));
                let domains = g.nodes[body.0]
                    .scope
                    .quantifiers
                    .iter()
                    .filter_map(|q| q.domain)
                    .collect::<Vec<_>>();
                assert!(!domains.is_empty());
                for domain in domains {
                    assert!(domain.0 < body.0);
                    assert_eq!(data(&g, domain).scope_domain_type(), Some(&Type::Bool));
                    let Part::ReadingDomain {
                        elements: Some(elements),
                        ..
                    } = data(&g, domain).part()
                    else {
                        panic!("finite Domain")
                    };
                    assert_eq!(
                        elements
                            .iter()
                            .map(|r| g.scalar(*r).unwrap().clone())
                            .collect::<Vec<_>>(),
                        vec![Scalar::Bool(false), Scalar::Bool(true)]
                    );
                }
            } else {
                assert_eq!(boolean(&g, r.holds), Some(true));
            }
        }
    }
    replay(&p, &g, &g.nodes).unwrap();
}

fn prefix(original: &Graph, c: &Control) -> Graph {
    let mut g = Graph::new(c);
    g.nodes = original.nodes.clone();
    g.contexts = original.contexts.clone();
    g.frames = original.frames.clone();
    g.iterations = original.iterations.clone();
    g.instances = original.instances.clone();
    g.cases = original.cases.clone();
    g.universal_witnesses = original.universal_witnesses.clone();
    g.active = original.active;
    g.requests = original.requests.clone();
    g.checked_answers = original.checked_answers.clone();
    g
}
#[test]
fn polynomial_reading_interrupt_keeps_exact_completed_boolean_prefixes() {
    use std::{cell::Cell, rc::Rc};
    let p = prepared(false, false, BODY, "root");
    let (initial, a) = built(&p);
    let before = initial.nodes.len();
    let mut complete = prefix(&initial, &quiet());
    let ds = retain_family(&mut complete, p.shared_inputs(), a, &quiet()).unwrap();
    for at in [
        2 * (ds[1].readings[0].holds.unwrap().0 - before + 1),
        2 * (ds[2].readings[0].holds.unwrap().0 - before + 1),
    ] {
        let seen = Rc::new(Cell::new(0));
        let count = seen.clone();
        let c = Control::new(move |point| {
            if point == Checkpoint::NativeResultNode {
                count.set(count.get() + 1);
            }
            let stop = count.get() >= at;
            stop.then_some(crate::result::Signal::Int)
        });
        let mut g = prefix(&initial, &c);
        assert!(matches!(
            retain_family(&mut g, p.shared_inputs(), a, &c),
            Err(ValidationFailure::Stop(_))
        ));
        assert_eq!(g.nodes.len(), before + at.div_ceil(2));
        assert_eq!(g.nodes.len(), g.contexts.len());
        for (left, right) in g.nodes.iter().zip(&complete.nodes) {
            assert_eq!(
                (
                    &left.ty,
                    &left.rule,
                    &left.arguments,
                    &left.support,
                    &left.scope,
                    &left.reasons,
                    &left.judgment
                ),
                (
                    &right.ty,
                    &right.rule,
                    &right.arguments,
                    &right.support,
                    &right.scope,
                    &right.reasons,
                    &right.judgment
                )
            );
            match (&left.payload, &right.payload) {
                (Some(Payload::Construction(a)), Some(Payload::Construction(b))) => {
                    assert_eq!(a.wire(), b.wire())
                }
                _ => assert_eq!(left, right),
            }
        }
        replay(&p, &g, &g.nodes).unwrap();
    }
}

#[test]
fn polynomial_tuple_reading_is_one_original_law_truth_and_keeps_both_numeric_components() {
    let p = prepared(
        false,
        true,
        "law required pair(c:Part):c.quantity=(0,rat(1,2));",
        "root",
    );
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &quiet()).unwrap();
    for (object, d) in ds.iter().enumerate() {
        assert_eq!(d.readings.len(), 2);
        assert_eq!(d.coordinates.len(), 4);
        for r in &d.readings {
            let (_, bindings) = origin(&g, r);
            let who = subject(&g, bindings);
            let applies = object == 0 || (object == 1 && who == "p") || (object == 2 && who == "q");
            assert_eq!(boolean(&g, r.body), applies.then_some(who == "p"));
            assert_eq!(boolean(&g, r.holds), Some(!applies || who == "p"));
        }
    }
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn polynomial_empty_and_symbolic_scalar_families_do_not_invent_concrete_readings() {
    let p = prepared(false, false, BODY, "r2");
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &quiet()).unwrap();
    assert_eq!(ds.len(), 1);
    assert!(ds[0].originals.is_empty() && ds[0].readings.is_empty());
    replay(&p, &g, &g.nodes).unwrap();
    let p = prepared(
        false,
        false,
        "law required symbolic(c:Part,k:Z):c.quantity=k;",
        "root",
    );
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &quiet()).unwrap();
    for d in &ds {
        assert!(d.readings.is_empty());
        assert!(d.unavailable.is_none());
        assert!(!d.coordinates.is_empty());
        for coordinate in &d.coordinates {
            let Part::Polynomial { parameters, .. } = data(&g, coordinate.nu.unwrap()).part()
            else {
                panic!("polynomial family")
            };
            assert_eq!(parameters, &vec![("k".into(), Type::Z)]);
        }
        assert!(
            d.originals
                .iter()
                .all(|o| o.parameters.iter().any(|(n, t)| n == "k" && t == &Type::Z))
        );
    }
    replay(&p, &g, &g.nodes).unwrap();
}

#[test]
fn polynomial_missing_guard_and_nonconstant_body_stay_unknown() {
    let p = prepared(
        true,
        false,
        "law required guarded(c:Part) when c.quantity=0:c.quantity=1;",
        "root",
    );
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &quiet()).unwrap();
    for (object, d) in ds.iter().enumerate() {
        assert_eq!(d.readings.len(), 2);
        for r in &d.readings {
            let (_, bindings) = origin(&g, r);
            let who = subject(&g, bindings);
            let applies = object == 0 || (object == 1 && who == "p") || (object == 2 && who == "q");
            assert_eq!(
                boolean(&g, r.body),
                (applies && who == "p").then_some(false)
            );
            assert_eq!(
                boolean(&g, r.holds),
                if !applies {
                    Some(true)
                } else if who == "p" {
                    Some(false)
                } else {
                    None
                }
            );
        }
    }
    replay(&p, &g, &g.nodes).unwrap();
}

#[test]
fn polynomial_unknown_guard_keeps_an_independently_evaluated_false_body() {
    let p = prepared(
        true,
        false,
        "law required guarded(c:Part) when c.quantity=0:false;",
        "root",
    );
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &quiet()).unwrap();
    for (object, d) in ds.iter().enumerate() {
        for r in &d.readings {
            let (_, bindings) = origin(&g, r);
            let who = subject(&g, bindings);
            let applies = object == 0 || (object == 1 && who == "p") || (object == 2 && who == "q");
            assert_eq!(boolean(&g, r.body), applies.then_some(false));
            assert_eq!(
                boolean(&g, r.holds),
                if !applies {
                    Some(true)
                } else if who == "p" {
                    Some(false)
                } else {
                    None
                }
            );
        }
    }
    replay(&p, &g, &g.nodes).unwrap();
}

#[test]
fn polynomial_unbounded_quantifier_domains_keep_z_and_reject_corrupted_prior_domain_records() {
    let p = prepared(
        false,
        false,
        "law required reflexive(c:Part):forall k:Z.k=k;law optional zero(c:Part):forall k:Z.k=0;",
        "root",
    );
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &quiet()).unwrap();
    let mut checked = None;
    for (object, d) in ds.iter().enumerate() {
        assert_eq!(d.readings.len(), 4);
        for r in &d.readings {
            let (name, bindings) = origin(&g, r);
            let who = subject(&g, bindings);
            let applies = object == 0 || (object == 1 && who == "p") || (object == 2 && who == "q");
            let truth = name.ends_with("reflexive");
            assert_eq!(boolean(&g, r.body), applies.then_some(truth));
            assert_eq!(boolean(&g, r.holds), Some(!applies || truth));
            if applies {
                let body = r.body.unwrap();
                let q = g.nodes[body.0]
                    .scope
                    .quantifiers
                    .iter()
                    .find(|q| q.name == "k")
                    .unwrap();
                assert_eq!(q.ty, Type::Z);
                assert_eq!(q.kind, crate::law::ast::QuantKind::Forall);
                let domain = q.domain.unwrap();
                assert!(domain.0 < body.0);
                assert!(matches!(
                    data(&g, domain).part(),
                    Part::ReadingDomain {
                        ty: Type::Z,
                        elements: None
                    }
                ));
                checked = Some((body, domain));
            }
        }
    }
    replay(&p, &g, &g.nodes).unwrap();
    let (body, domain) = checked.unwrap();
    let mut bad = prefix(&g, &quiet());
    bad.nodes.truncate(body.0);
    bad.contexts.truncate(body.0);
    let Some(Payload::Construction(v)) = &mut bad.nodes[domain.0].payload else {
        panic!("native")
    };
    let D::PolynomialLaw(d) = &mut v.data else {
        panic!("Domain")
    };
    d.index = usize::MAX;
    assert!(bad.push(g.nodes[body.0].clone()).is_err());
}

fn explicit_domain_readings(
    body: &str,
    count: usize,
    mut check: impl FnMut(&Graph, NodeRef, &str),
) {
    let p = prepared(false, false, body, "root");
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &quiet()).unwrap();
    assert_eq!(ds.len(), 3);
    let mut domains = 0;
    for (object, d) in ds.iter().enumerate() {
        assert_eq!(d.readings.len(), 2);
        for r in &d.readings {
            let (_, bindings) = origin(&g, r);
            let who = subject(&g, bindings);
            let applies = object == 0 || (object == 1 && who == "p") || (object == 2 && who == "q");
            assert_eq!(boolean(&g, r.body), applies.then_some(true));
            assert_eq!(boolean(&g, r.holds), Some(true));
            if let Some(body) = r.body {
                let q = g.nodes[body.0]
                    .scope
                    .quantifiers
                    .iter()
                    .find(|q| q.name == "f")
                    .unwrap();
                let domain = q.domain.unwrap();
                assert!(domain.0 < body.0);
                let Part::ReadingDomain {
                    ty,
                    elements: Some(elements),
                } = data(&g, domain).part()
                else {
                    panic!("finite Domain")
                };
                assert_eq!(ty, &q.ty);
                assert_eq!(elements.len(), count);
                for &element in elements {
                    assert!(element.0 < domain.0);
                    assert_eq!(g.scalar(element).unwrap().ty(), q.ty);
                    check(&g, element, &who);
                }
                domains += 1;
            }
        }
    }
    assert_eq!(domains, 4);
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn polynomial_explicit_term_domains_keep_both_closed_terms_and_boolean_readings() {
    let mut bodies = std::collections::BTreeSet::new();
    explicit_domain_readings(
        "law required term(c:Part):forall f in list<Term<(Z)->Z>>[fn(x:Z)=>x,fn(x:Z)=>x+1].f(0)>=0;",
        2,
        |g, r, _| {
            let Scalar::Term(term) = g.scalar(r).unwrap() else {
                panic!("Term")
            };
            assert_eq!(term.params, vec![("x".into(), Type::Z)]);
            assert_eq!(term.returns, Type::Z);
            bodies.insert(term.body.clone());
            assert_eq!(data(g, r).wire(), term.wire());
        },
    );
    assert_eq!(
        bodies,
        std::collections::BTreeSet::from(["x".into(), "x+1".into()])
    );
}
#[test]
fn polynomial_explicit_path_domains_keep_typed_endpoints_and_prior_wire_dependencies() {
    explicit_domain_readings(
        "law required walkKnown(c:Part):forall f in list<Path<Part,Part>>[identity(c),identity(c)].source(f)=c;",
        1,
        |g, r, who| {
            let Scalar::Path(path) = g.scalar(r).unwrap() else {
                panic!("Path")
            };
            assert_eq!(path.subject, who);
            assert_eq!(path.entity, "Family.Part");
            assert_eq!(path.reading, "Selected");
            assert!(path.step.is_none());
            let part = data(g, r);
            let args = part.part().arguments();
            assert_eq!(args.len(), 2);
            assert!(args.iter().all(|a| a.0 < r.0));
            for &a in &args {
                assert_eq!(g.scalar(a).unwrap(), &path.object());
            }
            assert_eq!(
                part.wire(),
                crate::observed::path_value::wire(g.scalar(r).unwrap(), &g.nodes, &args, &quiet())
                    .unwrap()
            );
        },
    );
}
#[test]
fn polynomial_explicit_nested_term_and_path_domains_keep_container_types_and_refs() {
    for (ty, values) in [
        (
            "List<Term<(Z)->Z>>",
            "list<Term<(Z)->Z>>[fn(x:Z)=>x],list<Term<(Z)->Z>>[]",
        ),
        (
            "List<Path<Part,Part>>",
            "list<Path<Part,Part>>[identity(c)],list<Path<Part,Part>>[]",
        ),
        (
            "Option<Path<Part,Part>>",
            "some(identity(c)),none<Path<Part,Part>>",
        ),
        ("(Path<Part,Part>,Z)", "(identity(c),0),(identity(c),1)"),
    ] {
        let law = format!("law required nested(c:Part):forall f in list<{ty}>[{values}].true;");
        explicit_domain_readings(&law, 2, |g, r, _| {
            let s = g.scalar(r).unwrap();
            let args = data(g, r).part().arguments();
            assert!(args.iter().all(|a| a.0 < r.0));
            assert_eq!(
                data(g, r).wire(),
                crate::observed::path_value::wire(s, &g.nodes, &args, &quiet()).unwrap()
            );
        });
    }
}
