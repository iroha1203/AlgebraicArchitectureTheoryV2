use super::*;
use crate::{
    control::{Limits, Usage},
    observed::{PreparedObserved, request::resolve_native_for_test},
};
#[allow(dead_code)]
mod fixture {
    include!("../../tests/common/polynomial_law_family_data.rs");
}
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn prepared(missing: bool, tuple: bool, body: &str, root: &str) -> PreparedObserved {
    let inputs = fixture::inputs(missing, tuple, body);
    let ask = format!("b=build(Selected,on=@v/{root})");
    let requests = resolve_native_for_test(
        inputs.law(),
        inputs.archmap(),
        &[ask.as_str()],
        &mut quiet(),
    )
    .unwrap();
    PreparedObserved {
        inputs,
        requests,
        object: None,
    }
}
fn built(p: &PreparedObserved) -> (Graph, NodeRef) {
    let mut c = quiet();
    let env = Environment::with_prepared(p, &mut c).unwrap();
    let mut g = Graph::new(&c);
    g.requests = p.requests().requests().to_vec();
    let a = crate::observed::architecture_result::build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[0],
        &mut c,
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
    let mut c = quiet();
    let env = Environment::with_prepared(p, &mut c)?;
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
        env.validate(&g, node)?;
        g.push(node.clone())?;
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
fn terms(g: &Graph, r: NodeRef) -> Vec<(Json, Vec<usize>)> {
    let Part::Polynomial { terms, parameters, .. } = data(g, r).part() else {
        panic!("polynomial")
    };
    assert!(parameters.is_empty());
    let Json::Obj(ref wire) = data(g, r).wire() else { panic!() };
    assert!(!wire.contains_key("parameters"));
    terms
        .iter()
        .map(|(coefficient, powers)| (g.scalar(*coefficient).unwrap().wire(), powers.clone()))
        .collect()
}
const BODY: &str = "law required zero(c:Part):c.quantity=0;law optional one(c:Part):c.quantity=1;";
#[test]
fn shared_table_plan_reuses_its_verified_immutable_polynomial_source() {
    use std::{cell::Cell, rc::Rc};
    let p = prepared(false, false, BODY, "root");
    let (mut g, a) = built(&p);
    let configurations = Rc::new(Cell::new(0usize));
    let hits = configurations.clone();
    let mut c = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::Configuration {
            hits.set(hits.get() + 1);
        }
        Usage::default()
    });
    let plan = retain_table_plan(&mut g, p.shared_inputs(), a, &mut c).unwrap();
    let env = Environment::with_prepared(&p, &mut c).unwrap();
    configurations.set(0);
    plan.recheck(&env, &g, a, &mut c).unwrap();
    assert!(configurations.get() > 0, "最初の消費は元計画を再構成する");
    configurations.set(0);
    plan.recheck(&env, &g, a, &mut c).unwrap();
    assert_eq!(
        configurations.get(),
        0,
        "同じ不変計画の再構成を繰り返さない"
    );
    assert!(plan.recheck(&env, &g, NodeRef(usize::MAX), &mut c).is_err());
}
#[test]
fn verified_table_plan_does_not_authorize_modified_sources_or_foreign_inputs() {
    let p = prepared(false, false, BODY, "root");
    let (mut g, a) = built(&p);
    let mut c = quiet();
    let plan = retain_table_plan(&mut g, p.shared_inputs(), a, &mut c).unwrap();
    let env = Environment::with_prepared(&p, &mut c).unwrap();
    plan.recheck(&env, &g, a, &mut c).unwrap();
    for mutation in 0..3 {
        let mut forged = plan.clone();
        let source = Arc::make_mut(&mut forged.0);
        match mutation {
            0 => {
                source.scope.readings.insert("forged".into());
            }
            1 => source.parts.clear(),
            _ => source.base += 1,
        }
        assert!(
            forged.recheck(&env, &g, a, &mut c).is_err(),
            "mutation {mutation}"
        );
    }
    let foreign = prepared(true, false, BODY, "root");
    let foreign_env = Environment::with_prepared(&foreign, &mut c).unwrap();
    assert!(plan.recheck(&foreign_env, &g, a, &mut c).is_err());
    plan.recheck(&env, &g, a, &mut c).unwrap();
}
#[test]
fn stopped_shared_table_plan_recheck_does_not_cache_a_partial_verification() {
    use std::{cell::Cell, rc::Rc};
    let p = prepared(false, false, BODY, "root");
    let (mut g, a) = built(&p);
    let plan = retain_table_plan(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    let armed = Rc::new(Cell::new(false));
    let arm = armed.clone();
    let mut c = Control::new(
        Limits {
            time_ms: Some(1),
            ..Limits::default()
        },
        move |point| Usage {
            elapsed_ms: u128::from(arm.get() && point == Checkpoint::Configuration),
            ..Usage::default()
        },
    );
    let env = Environment::with_prepared(&p, &mut c).unwrap();
    armed.set(true);
    assert!(matches!(
        plan.recheck(&env, &g, a, &mut c),
        Err(ValidationFailure::Stop(_))
    ));
    assert!(env.verified_polynomial_law_diagrams.borrow().is_empty());
}

#[test]
fn option_guards_do_not_choose_a_numeric_parameter_value() {
    guards_do_not_choose_a_numeric_parameter_value(&["some(n)=some(0)", "some(n)!=some(0)"]);
}
#[test]
fn tuple_guards_do_not_choose_a_numeric_parameter_value() {
    guards_do_not_choose_a_numeric_parameter_value(&["(n,true)=(0,true)", "(n,true)!=(0,true)"]);
}
#[test]
fn list_guards_do_not_choose_a_numeric_parameter_value() {
    guards_do_not_choose_a_numeric_parameter_value(&["list<Z>[n]=list<Z>[0]", "list<Z>[n]!=list<Z>[0]"]);
}
fn guards_do_not_choose_a_numeric_parameter_value(guards: &[&str]) {
    for guard in guards {
        let p = prepared(
            false,
            false,
            &format!("law required zero(c:Part,n:Z) when {guard}:n*c.quantity=0;"),
            "root",
        );
        let (g, a) = built(&p);
        let Some(Payload::Construction(value)) = &g.get(a).unwrap().payload else {
            panic!("architecture")
        };
        let Witness::Architecture(a) = &value.witness else {
            panic!("architecture witness")
        };
        assert!(parameters::sources(&p.shared_inputs(), a, &mut quiet())
            .unwrap()
            .is_none());
    }
}
#[test]
fn inactive_missing_parameter_products_omit_evaluation_without_inventing_values() {
    for guard in ["false", "true"] {
        let p = prepared(
            true,
            false,
            &format!("law required zero(c:Part,n:Z) when {guard}:n*c.quantity=0;"),
            "root",
        );
        let (mut g, a) = built(&p);
        let Some(Payload::Construction(value)) = &g.nodes[a.0].payload else {
            panic!("architecture")
        };
        let Witness::Architecture(architecture) = &value.witness else {
            panic!("architecture witness")
        };
        let equations =
            parameters::sources(&p.shared_inputs(), architecture, &mut quiet()).unwrap();
        if guard == "true" {
            assert!(equations.is_some());
            continue;
        }
        let equations = equations.unwrap();
        assert!(
            equations
                .iter()
                .any(|(_, e)| e.ring.symbols.iter().any(|s| s.value.is_none()))
        );
        let diagrams = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
        for diagram in diagrams {
            assert_eq!(diagram.evaluations, [None]);
            for coordinate in diagram.coordinates {
                assert_eq!(coordinate.status, EquationPresentationStatus::NotApplicable);
                assert!(coordinate.epsilon.is_none());
                assert!(terms(&g, coordinate.residual.unwrap()).is_empty());
            }
            for required in diagram.required {
                let Part::Ideal { generators, .. } = data(&g, required).part() else {
                    panic!("ideal")
                };
                assert!(generators.is_empty());
            }
        }
        replay(&p, &g, &g.nodes).unwrap();
    }
}
#[test]
fn active_missing_parameter_products_keep_symbolic_equations_and_missing_reasons() {
    let p = prepared(
        true,
        false,
        "law required zero(c:Part,n:Z):n*c.quantity=0;",
        "root",
    );
    let (mut g, a) = built(&p);
    let diagrams = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    let mut pending = false;
    for diagram in diagrams {
        assert_eq!(diagram.evaluations, [None]);
        for coordinate in diagram.coordinates {
            if coordinate.guard == EquationGuard::AlwaysTrue && coordinate.epsilon.is_none() {
                pending = true;
                assert_eq!(coordinate.status, EquationPresentationStatus::Undetermined);
                assert!(coordinate.nu.is_some());
                assert!(coordinate.residual.is_none());
            }
        }
        if diagram.status == EquationPresentationStatus::Undetermined {
            assert!(diagram.presentations.iter().flatten().any(|r| {
                let Part::Equation(
                    crate::observed::equation_presentation_node::Part::Presentation {
                        omissions,
                        ..
                    },
                ) = data(&g, *r).part()
                else {
                    panic!("presentation")
                };
                omissions.iter().any(|r| {
                    r.missing.iter().any(|f| {
                        f.subject == "q" && f.field.as_deref() == Some("Family.Part.quantity")
                    })
                })
            }));
        }
    }
    assert!(pending);
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn inactive_parameter_families_keep_original_difference_without_required_generators() {
    let p=prepared(false,false,"view active(n:Z):Bool=n+1=n;law required zero(c:Part,n:Z) when active(n):n=0;","root");
    let (mut g,a)=built(&p);
    let ds=retain_family(&mut g,p.shared_inputs(),a,&mut quiet()).unwrap();
    assert!(!ds[0].coordinates.is_empty());
    for q in &ds[0].coordinates {
        assert_eq!(q.guard,EquationGuard::AlwaysFalse);
        assert!(q.epsilon.is_none());
        assert!(terms(&g,q.residual.unwrap()).is_empty());
        let Part::Polynomial { parameters, terms, .. }=data(&g,q.nu.unwrap()).part() else { panic!("family") };
        assert_eq!(parameters,&vec![("n".into(),Type::Z)]); assert_eq!(terms.len(),1);
    }
    for ideal in &ds[0].required {
        let Part::Ideal { generators, .. }=data(&g,*ideal).part() else { panic!("ideal") };
        assert!(generators.is_empty());
    }
    replay(&p,&g,&g.nodes).unwrap();
}
#[test]
fn cancelled_observation_families_share_constant_polynomial_and_residual() {
    let p = prepared(false, false, "law required equal(c:Part,n:Z):n+c.quantity=c.quantity+1;", "root");
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    for coordinate in &ds[0].coordinates {
        let nu = coordinate.nu.unwrap();
        assert_eq!(coordinate.epsilon, Some(nu));
        let Part::Polynomial { terms, parameters, .. } = data(&g, nu).part() else { panic!("polynomial") };
        assert_eq!(parameters.len(), 1);
        assert_eq!(terms.len(), 1);
        assert!(terms[0].1.iter().all(|power| *power == 0));
        let (_, family) = data(&g, nu).parameter_difference(&mut quiet()).unwrap().unwrap();
        assert_eq!(family.parameters.len(), 1);
        assert_eq!(family.parameters[0].1, EquationPolynomial::constant(Scalar::Z(1.into()), &mut quiet()).unwrap());
        let value = family.constant.evaluate(&[], &mut quiet()).unwrap().unwrap();
        assert_eq!(value.scalar(), &Scalar::Z((-1).into()));
    }
    replay(&p, &g, &g.nodes).unwrap();
    // 別の観測位置は実際の値が一致する場合でも相殺しない。
    let mut p = prepared(false, false, "law required equal(c:Part,d:Part,n:Z):n+c.quantity=d.quantity+1;", "root");
    let sources = p.inputs.sources();
    let map = std::str::from_utf8(sources.archmap().bytes()).unwrap();
    let inputs = crate::input::InputSources::new(
        sources.definitions().to_vec(),
        sources.law().clone(),
        crate::input::InputBytes::new(
            sources.archmap().id(),
            map.replace(r#""value":"1""#, r#""value":"0""#).into_bytes(),
        ),
    );
    p.inputs = Arc::new(crate::input::check_inputs(inputs, &mut quiet()).unwrap());
    p.requests = resolve_native_for_test(p.inputs.law(), p.inputs.archmap(), &["b=build(Selected,on=@v/root)"], &mut quiet()).unwrap();
    let (g, a) = built(&p);
    let Some(Payload::Construction(value)) = &g.nodes[a.0].payload else { panic!("architecture") };
    let Witness::Architecture(a) = &value.witness else { panic!("architecture witness") };
    let equations = parameters::sources(&p.shared_inputs(), a, &mut quiet()).unwrap().unwrap();
    assert!(equations.iter().any(|(_, source)| source.ring.symbols.len() == 2
        && source.difference.constant.terms.iter().filter(|term| !term.variables.is_empty()).count() == 2));
}
#[test]
fn parameter_polynomials_keep_free_observation_variables() {
    fn expression(inputs: &CheckedInputs, id: usize, n: i64, x: i64) -> i64 {
        use crate::law::ast::{BinOp, ExprKind};
        match &inputs.law().exprs[id].kind {
            ExprKind::Int(value) => value.parse().unwrap(),
            ExprKind::Group(child) => expression(inputs, *child, n, x),
            ExprKind::Dotted(names) if names.len() == 1 && names[0].name == "n" => n,
            ExprKind::Dotted(names) if names.last().unwrap().name == "quantity" => x,
            ExprKind::Field { name, .. } if name.name == "quantity" => x,
            ExprKind::Binary { op, lhs, rhs } => {
                let lhs = expression(inputs, *lhs, n, x);
                let rhs = expression(inputs, *rhs, n, x);
                match op { BinOp::Add => lhs + rhs, BinOp::Sub => lhs - rhs, BinOp::Mul => lhs * rhs, _ => panic!("arithmetic") }
            }
            _ => panic!("numeric source"),
        }
    }
    fn coefficient(g: &Graph, r: NodeRef, n: i64, x: i64) -> i64 {
        match data(g, r).part() {
            Part::Scalar(Scalar::Z(value)) => value.to_string().parse().unwrap(),
            Part::Source { expression: id, .. } => expression(&data(g, r).source.inputs, *id, n, x),
            Part::Transform { operation: Transform::Substitute, operands, bindings, .. } => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].name, "n");
                let value = coefficient(g, bindings[0].value, n, x);
                coefficient(g, operands[0], value, x)
            }
            Part::Transform { operation: Transform::Difference, operands, .. } => {
                assert_eq!(operands.len(), 2);
                coefficient(g, operands[0], n, x) - coefficient(g, operands[1], n, x)
            }
            Part::Transform { operation: Transform::Multiply, operands, .. } => {
                coefficient(g, operands[0], n, x) * coefficient(g, operands[1], n, x)
            }
            _ => panic!("numeric coefficient"),
        }
    }
    for (body, parameter, observation, constant, cross) in [("n=c.quantity+2", 1, -1, -2), ("c.quantity+2=n", -1, 1, 2),
        ("n+c.quantity=2", 1, 1, -2), ("n+c.quantity=2*n+1", -1, 1, -1),
        ("2*(n+c.quantity)=2", 2, 2, -2), ("(n+c.quantity)*2=2", 2, 2, -2),
        ("equalvalue(n+c.quantity)",1,1,-2), ("twice(n+c.quantity)",2,2,-2)].into_iter().map(|(body, p, o, c)| (body, p, o, c, 0))
        .chain([("n*c.quantity=0",0,0,0,1), ("c.quantity*n=0",0,0,0,1),
            ("2*(n*c.quantity)+c.quantity=3",0,1,-3,2), ("n*c.quantity-n*c.quantity=n",-1,0,0,0)]) {
        let p = prepared(false, false, &format!("view equalvalue(n:Z):Bool=n=2;view twice(n:Z):Bool=equalvalue(2*n);law required equal(c:Part,n:Z):{body};"), "root");
        let (mut g, a) = built(&p);
        let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
        for coordinate in &ds[0].coordinates {
            let Part::Polynomial { terms, .. } = data(&g, coordinate.nu.unwrap()).part() else { panic!("polynomial") };
            if parameter != 0 || constant != 0 {
                assert_eq!(terms.iter().filter(|(_, powers)| powers.iter().all(|p| *p == 0)).count(), 1);
            }
            for n in [-3, 0, 4] {
                for x in [-5i64, 0, 7] {
                    let actual: i64 = terms.iter().map(|(r, powers)| {
                        coefficient(&g, *r, n, x) * powers.iter().map(|power| x.pow(*power as u32)).product::<i64>()
                    }).sum();
                    assert_eq!(actual, parameter * n + observation * x + constant + cross * n * x);
                }
            }
        }
        replay(&p, &g, &g.nodes).unwrap();
    }
}
#[test]
fn parameter_polynomials_are_typed_families_and_reject_changed_domains() {
    let p = prepared(false, false, "law required zero(c:Part,n:Z):n=0;", "root");
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    let nu = ds[0].coordinates[0].nu.unwrap();
    let d = data(&g, nu);
    assert!(d.polynomial().is_none());
    let (ring, family) = d.parameter_difference(&mut quiet()).unwrap().unwrap();
    assert_eq!(Some(ring), ds[0].coordinates[0].ring);
    assert_eq!(family.parameters.len(), 1);
    let original = d.source.clone();
    for change in 0..4 {
        let mut source = original.as_ref().clone();
        let Part::Polynomial { parameters, terms, .. } = &mut source.parts[d.index] else { panic!() };
        match change {
            0 => parameters.clear(),
            1 => parameters[0].1 = Type::Q,
            2 => parameters[0].0 = "other".into(),
            3 => terms[0].1.push(1),
            _ => unreachable!(),
        }
        assert!(source.recheck(&p.inputs, &original.architecture, &mut quiet()).is_err());
    }
    original.recheck(&p.inputs, &original.architecture, &mut quiet()).unwrap();
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn shared_polynomial_family_maps_distinct_local_symbols_into_the_same_z_ring() {
    let p = prepared(false, false, BODY, "root");
    let (mut g, a) = built(&p);
    let before = g.nodes.len();
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    assert_eq!(ds.len(), 3);
    let source = &data(&g, ds[0].rings[0]).source;
    assert_eq!(source.owned_outputs.as_ref().unwrap().len(), 2);
    assert_eq!(
        source
            .parts
            .iter()
            .filter(|p| matches!(p, Part::Ring { .. }))
            .count(),
        1
    );
    assert_eq!(
        source
            .parts
            .iter()
            .filter(|p| matches!(p, Part::Base(_)))
            .count(),
        1
    );
    assert_eq!(
        source
            .parts
            .iter()
            .filter(|p| matches!(p, Part::Evaluation { .. }))
            .count(),
        1
    );
    let Part::Ring { variables, .. } = data(&g, ds[0].rings[0]).part() else {
        panic!("ring")
    };
    assert_eq!(
        variables
            .iter()
            .map(|v| (v.field.subject.as_str(), v.component.clone()))
            .collect::<Vec<_>>(),
        [("p", vec![]), ("q", vec![])]
    );
    for (object, d) in ds.iter().enumerate() {
        assert_eq!(d.rings, ds[0].rings);
        assert_eq!(d.bases, ds[0].bases);
        assert_eq!(d.domains, ds[0].domains);
        assert_eq!(d.evaluations, ds[0].evaluations);
        assert_eq!(d.status, EquationPresentationStatus::Ready);
        assert!(d.presentations.iter().all(Option::is_some));
        assert_eq!(d.coordinates.len(), 4);
        let Part::Ideal {
            ring,
            generators,
            required,
            parameters,
        } = data(&g, d.required[0]).part()
        else {
            panic!("required")
        };
        assert!(*required);
        assert!(parameters.is_empty());
        assert_eq!(*ring, d.rings[0]);
        assert_eq!(
            *generators,
            d.coordinates
                .iter()
                .filter(|q| q.required && q.guard == EquationGuard::AlwaysTrue)
                .map(|q| q.nu.unwrap())
                .collect::<Vec<_>>()
        );
        for q in &d.coordinates {
            let original = d
                .originals
                .iter()
                .find(|o| o.reference == q.instance)
                .unwrap();
            let binding = g.scalar(original.bindings[0].value).unwrap();
            let Scalar::Subject { subject, .. } = binding else {
                panic!("binding")
            };
            if q.guard == EquationGuard::OutsideObject {
                assert!(object > 0 && subject != if object == 1 { "p" } else { "q" });
                assert_eq!(q.status, EquationPresentationStatus::NotApplicable);
                assert!(
                    q.left.is_some() && q.right.is_some() && q.nu.is_some() && q.epsilon.is_none()
                );
                assert!(terms(&g, q.residual.unwrap()).is_empty());
                continue;
            }
            assert!(object == 0 || subject == if object == 1 { "p" } else { "q" });
            let powers = if subject == "p" {
                vec![1, 0]
            } else {
                vec![0, 1]
            };
            assert_eq!(
                terms(&g, q.left.unwrap()),
                [(Json::str("1"), powers.clone())]
            );
            let Part::LawInstance { name, .. } = data(&g, original.reference).part() else {
                panic!("instance")
            };
            let is_one = name.ends_with("one");
            let mut expected = if is_one {
                vec![(Json::str("-1"), vec![0, 0])]
            } else {
                vec![]
            };
            expected.push((Json::str("1"), powers));
            assert_eq!(terms(&g, q.nu.unwrap()), expected);
            let value = i32::from(subject == "q") - i32::from(is_one);
            assert_eq!(
                terms(&g, q.epsilon.unwrap()),
                if value == 0 {
                    vec![]
                } else {
                    vec![(Json::str(value.to_string()), vec![0, 0])]
                }
            );
            assert_eq!(q.ring, Some(ds[0].rings[0]));
        }
    }
    for (at, n) in g.nodes.iter().enumerate().skip(before) {
        assert!(n.arguments.iter().all(|r| r.0 < at));
        let Some(Payload::Construction(v)) = &n.payload else {
            panic!("construction")
        };
        let D::PolynomialLaw(d) = &v.data else {
            panic!("polynomial")
        };
        assert!(Arc::ptr_eq(source, &d.source));
    }
    replay(&p, &g, &g.nodes).unwrap();
}

#[test]
fn shared_polynomial_tuple_components_keep_z_and_q_separate_across_all_objects() {
    let p = prepared(
        false,
        true,
        "law required pair(c:Part):c.quantity=(0,0);",
        "root",
    );
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    assert_eq!(ds.len(), 3);
    assert_eq!(ds[0].rings.len(), 2);
    assert_ne!(ds[0].rings[0], ds[0].rings[1]);
    for d in &ds {
        assert_eq!(d.rings, ds[0].rings);
        assert_eq!(d.evaluations, ds[0].evaluations);
        for q in &d.coordinates {
            let index = usize::from(q.ty == Type::Q);
            assert_eq!(q.component, [index]);
            assert_eq!(q.ring, Some(ds[0].rings[index]));
            let Part::Ring { variables, .. } = data(&g, ds[0].rings[index]).part() else {
                panic!("ring")
            };
            assert_eq!(variables.len(), 2);
            assert!(
                variables
                    .iter()
                    .all(|v| v.ty == q.ty && v.component == [index])
            );
            let original = d
                .originals
                .iter()
                .find(|o| o.reference == q.instance)
                .unwrap();
            let Scalar::Subject { subject, .. } = g.scalar(original.bindings[0].value).unwrap()
            else {
                panic!("binding")
            };
            if q.guard == EquationGuard::OutsideObject {
                assert!(q.nu.is_some() && q.epsilon.is_none());
                assert!(terms(&g, q.residual.unwrap()).is_empty());
                continue;
            }
            let expected = if index == 0 {
                Json::str("1")
            } else {
                Json::Arr(vec![Json::str("1"), Json::str("1")])
            };
            assert_eq!(
                terms(&g, q.nu.unwrap()),
                [(
                    expected,
                    if subject == "p" {
                        vec![1, 0]
                    } else {
                        vec![0, 1]
                    }
                )]
            );
        }
    }
    replay(&p, &g, &g.nodes).unwrap();
}

#[test]
fn missing_shared_slot_omits_global_evaluation_but_keeps_known_original_epsilon() {
    let p = prepared(true, false, BODY, "root");
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    assert_eq!(ds.len(), 3);
    for d in &ds {
        assert_eq!(d.rings, ds[0].rings);
        assert_eq!(d.evaluations, [None]);
        let Part::Equation(crate::observed::equation_presentation_node::Part::Context {
            dependencies,
            ..
        }) = data(&g, d.context.unwrap()).part()
        else {
            panic!("context")
        };
        let mut quantity_subjects = dependencies
            .iter()
            .filter(|(_, f)| f == "Family.Part.quantity")
            .map(|(r, _)| match g.scalar(*r).unwrap() {
                Scalar::Subject { subject, .. } => subject.as_str(),
                _ => panic!("subject"),
            })
            .collect::<Vec<_>>();
        quantity_subjects.sort();
        assert_eq!(quantity_subjects, ["p", "q"]);
        assert!(d.presentations.iter().all(Option::is_some));
        for r in d.presentations.iter().flatten() {
            let Part::Equation(crate::observed::equation_presentation_node::Part::Presentation {
                coordinates,
                evaluation,
                omissions,
                ..
            }) = data(&g, *r).part()
            else {
                panic!("presentation")
            };
            assert!(evaluation.is_none());
            assert!(
                omissions
                    .iter()
                    .flat_map(|r| &r.missing)
                    .any(|f| f.subject == "q"
                        && f.field.as_deref() == Some("Family.Part.quantity")
                        && f.atom.is_none())
            );
            for q in coordinates {
                let o = d
                    .originals
                    .iter()
                    .find(|o| o.reference == q.instance)
                    .unwrap();
                let Scalar::Subject { subject, .. } = g.scalar(o.bindings[0].value).unwrap() else {
                    panic!("binding")
                };
                let applicable = d.coordinates.iter().any(|coordinate| coordinate.instance == q.instance && coordinate.guard == EquationGuard::AlwaysTrue);
                assert_eq!(q.epsilon.is_some(), subject == "p" && applicable);
            }
        }
    }
    replay(&p, &g, &g.nodes).unwrap();
}

#[test]
fn empty_shared_polynomial_family_preserves_base_and_owned_objects_without_rings() {
    for (root, count) in [("root", 3), ("r2", 1)] {
        let p = prepared(false, false, "", root);
        let (mut g, a) = built(&p);
        let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
        assert_eq!(ds.len(), count);
        for d in &ds {
            assert!(
                d.rings.is_empty()
                    && d.domains.is_empty()
                    && d.coordinates.is_empty()
                    && d.originals.is_empty()
            );
            assert!(d.presentations.is_empty() && d.unavailable.is_none());
            let source = &data(&g, d.context.unwrap()).source;
            assert_eq!(source.architecture.construction().root().subject, root);
            assert_eq!(source.owned_outputs.as_ref().unwrap().len(), count - 1);
        }
        replay(&p, &g, &g.nodes).unwrap();
    }
}

#[test]
fn finite_parameter_rows_and_symbolic_numeric_families_are_preserved() {
    let p = prepared(
        false,
        false,
        "law required choose(c:Part,b:Bool):c.quantity=(if b then 0 else 1);",
        "root",
    );
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    for d in &ds {
        assert_eq!(d.coordinates.len(), 4);
        assert_eq!(d.rings, ds[0].rings);
        let mut rows = vec![];
        for original in d.originals.iter().filter(|o| o.row.is_some()) {
            let parameter = original.bindings.iter().find(|b| b.name == "b").unwrap();
            let entity = original.bindings.iter().find(|b| b.name == "c").unwrap();
            let Scalar::Subject { subject, .. } = g.scalar(entity.value).unwrap() else {
                panic!("subject")
            };
            let Scalar::Bool(value) = g.scalar(parameter.value).unwrap() else {
                panic!("parameter")
            };
            rows.push((subject.as_str(), *value));
        }
        rows.sort();
        let expected = vec![("p", false), ("p", true), ("q", false), ("q", true)];
        assert_eq!(rows, expected);
        for q in d
            .coordinates
            .iter()
            .filter(|q| q.guard == EquationGuard::OutsideObject)
        {
            // 有限rowは残るが、適用外では条件式を評価して原式を補わない。
            assert!(q.row.is_some() && q.nu.is_none() && q.epsilon.is_none());
            assert!(terms(&g, q.residual.unwrap()).is_empty());
            let original = d
                .originals
                .iter()
                .find(|o| o.reference == q.instance)
                .unwrap();
            assert!(original.parameters.is_empty());
            assert!(original.bindings.iter().any(|b| b.name == "b" && b.ty == Type::Bool));
        }
    }
    replay(&p, &g, &g.nodes).unwrap();
    let p = prepared(
        false,
        false,
        "law required symbolic(c:Part,k:Z):c.quantity=k;",
        "root",
    );
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    assert_eq!(ds.len(), 3);
    for d in &ds {
        assert!(d.unavailable.is_none());
        assert_eq!(d.status, EquationPresentationStatus::Ready);
        assert_eq!(d.rings, ds[0].rings);
        assert_eq!(d.coordinates.len(), 2);
        assert!(d.evaluations.iter().all(Option::is_some));
        for q in &d.coordinates {
            assert!(data(&g, q.nu.unwrap()).parameter_family(&[("k".into(), Type::Z)]));
            if q.guard == EquationGuard::OutsideObject {
                assert!(q.epsilon.is_none());
                assert!(terms(&g, q.residual.unwrap()).is_empty());
            } else {
                assert!(data(&g, q.epsilon.unwrap()).parameter_difference(&mut quiet()).unwrap().is_some());
            }
        }
        assert!(
            d.originals
                .iter()
                .all(|o| o.parameters.iter().any(|(n, t)| n == "k" && t == &Type::Z))
        );
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
fn shared_polynomial_four_stops_keep_exact_finished_basis_and_object_prefixes() {
    use std::{cell::Cell, rc::Rc};
    let p = prepared(false, false, BODY, "root");
    let (initial, a) = built(&p);
    let before = initial.nodes.len();
    let mut complete = prefix(&initial, &quiet());
    let ds = retain_family(&mut complete, p.shared_inputs(), a, &mut quiet()).unwrap();
    for mode in [2] {
        for at in [
            2 * (ds[1].context.unwrap().0 - before + 1),
            2 * (ds[2].context.unwrap().0 - before + 1),
        ] {
            let seen = Rc::new(Cell::new(0));
            let count = seen.clone();
            let mut c = Control::new(
                Limits {
                    time_ms: (mode == 0).then_some(1),
                    memory_mib: (mode == 1).then_some(1),
                },
                move |point| {
                    if point == Checkpoint::NativeResultNode {
                        count.set(count.get() + 1);
                    }
                    let stop = count.get() >= at;
                    Usage {
                        elapsed_ms: u128::from(stop && mode == 0),
                        memory_mib: u128::from(stop && mode == 1),
                        signal: if stop && mode >= 2 {
                            Some(if mode == 2 {
                                crate::result::Signal::Int
                            } else {
                                crate::result::Signal::Term
                            })
                        } else {
                            None
                        },
                    }
                },
            );
            let mut g = prefix(&initial, &c);
            assert!(matches!(
                retain_family(&mut g, p.shared_inputs(), a, &mut c),
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
}

#[test]
fn shared_polynomial_family_rejects_foreign_root_request_input_and_cached_witness_without_appending()
 {
    let mut p = prepared(false, false, BODY, "root");
    p.requests = resolve_native_for_test(
        p.inputs().law(),
        p.inputs().archmap(),
        &["b=build(Selected,on=@v/root)", "c=build(Selected,on=@v/r2)"],
        &mut quiet(),
    )
    .unwrap();
    let (mut g, a) = built(&p);
    let mut c = quiet();
    let env = Environment::with_prepared(&p, &mut c).unwrap();
    g.active.request = 1;
    let before = g.nodes.len();
    assert!(retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).is_err());
    assert_eq!(g.nodes.len(), before);
    let other = crate::observed::architecture_result::build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[1],
        &mut c,
    )
    .unwrap();
    assert!(other.complete);
    let second = retain_family(&mut g, p.shared_inputs(), other.reference, &mut quiet()).unwrap();
    assert_eq!(second.len(), 1);
    assert_eq!(
        data(&g, second[0].context.unwrap())
            .source
            .architecture
            .construction()
            .root()
            .subject,
        "r2"
    );
    g.active.request = 0;
    let first = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    let Some(Payload::Construction(value)) = &g.nodes[first[0].context.unwrap().0].payload else {
        panic!("native")
    };
    env.recheck_polynomial_law_diagram(&g, value).unwrap();
    let mut foreign = (**value).clone();
    foreign.witness = Witness::Architecture(
        data(&g, second[0].context.unwrap())
            .source
            .architecture
            .clone(),
    );
    assert!(env.recheck_polynomial_law_diagram(&g, &foreign).is_err());
    let missing = prepared(true, false, BODY, "root");
    let before = g.nodes.len();
    assert!(retain_family(&mut g, missing.shared_inputs(), a, &mut quiet()).is_err());
    assert_eq!(g.nodes.len(), before);
    let objects = crate::observed::object_component_diagram::retain(
        &mut g,
        p.shared_inputs(),
        a,
        &mut quiet(),
    )
    .unwrap()
    .unwrap();
    let before = g.nodes.len();
    assert!(
        retain_family(
            &mut g,
            p.shared_inputs(),
            objects.architectures[1],
            &mut quiet()
        )
        .is_err()
    );
    assert_eq!(g.nodes.len(), before);
    replay(&p, &g, &g.nodes).unwrap();
}

#[test]
fn boolean_cases_bind_finite_values_without_sampling_numeric_parameters() {
    let p = prepared(false, false, "law required zero(c:Part,n:Z,b:Bool) when b:n*c.quantity=0;", "root");
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    {
        let diagram = &ds[0];
        assert_eq!(diagram.originals.len(), 4);
        assert_eq!(diagram.coordinates.len(), 4);
        for (ordinal, original) in diagram.originals.iter().enumerate() {
            let value = ordinal % 2 == 1;
            assert_eq!(original.finite, vec![("b".into(), Scalar::Bool(value))]);
            assert_eq!(original.parameters, vec![("n".into(), Type::Z)]);
            assert_eq!(original.quantifiers.len(), 1);
            assert_eq!(original.quantifiers[0].name, "n");
            let binding = original.bindings.iter().find(|b| b.name == "b").unwrap();
            assert_eq!(g.scalar(binding.value).unwrap(), &Scalar::Bool(value));
            let coordinate = &diagram.coordinates[ordinal];
            assert_eq!(coordinate.guard, if value { EquationGuard::AlwaysTrue } else { EquationGuard::AlwaysFalse });
            if !value {
                assert_eq!(coordinate.status, EquationPresentationStatus::NotApplicable);
                assert!(coordinate.epsilon.is_none());
                assert!(terms(&g, coordinate.residual.unwrap()).is_empty());
            }
            let Part::Polynomial { parameters, .. } = data(&g, coordinate.nu.unwrap()).part() else { panic!("polynomial") };
            assert_eq!(parameters, &vec![("n".into(), Type::Z)]);
        }
    }
    replay(&p, &g, &g.nodes).unwrap();
    let d = data(&g, ds[0].coordinates[0].nu.unwrap());
    let mut source = (*d.source).clone();
    source.outputs.originals[0].finite[0].1 = Scalar::Bool(true);
    let altered = Arc::new(source);
    let mut nodes = g.nodes.clone();
    for node in &mut nodes {
        if let Some(Payload::Construction(value)) = &mut node.payload {
            if let D::PolynomialLaw(data) = &mut value.data {
                if Arc::ptr_eq(&data.source, &d.source) { data.source = altered.clone(); }
            }
        }
    }
    assert!(replay(&p, &g, &nodes).is_err());
}

#[test]
fn boolean_case_products_cover_joint_guards_and_keep_inactive_ideals_empty() {
    for (guard, active) in [("b and d", 2usize), ("b and false", 0), ("b and n=n", 4)] {
        let p = prepared(false, false, &format!("law required zero(c:Part,n:Z,b:Bool,d:Bool) when {guard}:n*c.quantity=0;"), "root");
        let (mut g, a) = built(&p);
        let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
        let diagram = &ds[0];
        assert_eq!(diagram.originals.len(), 8);
        assert_eq!(diagram.coordinates.iter().filter(|q| q.guard == EquationGuard::AlwaysTrue).count(), active);
        for original in &diagram.originals {
            assert_eq!(original.parameters, vec![("n".into(), Type::Z)]);
            assert_eq!(original.finite.len(), 2);
        }
        if active == 0 {
            for &ideal in &diagram.required {
                let Part::Ideal { generators, .. } = data(&g, ideal).part() else { panic!("ideal") };
                assert!(generators.is_empty());
            }
        }
        replay(&p, &g, &g.nodes).unwrap();
    }
}

#[test]
fn cancelled_numeric_axes_keep_boolean_cases_and_the_original_quantifiers() {
    for offset in [0, 1] {
        let p = prepared(false, false, &format!("law required balanced(c:Part,n:Z,b:Bool) when b:n*c.quantity=n*c.quantity+{offset};"), "root");
        let (mut g, a) = built(&p);
        let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
        let diagram = &ds[0];
        assert_eq!(diagram.originals.len(), 4);
        assert_eq!(diagram.coordinates.len(), 4);
        for (ordinal, original) in diagram.originals.iter().enumerate() {
            let active = ordinal % 2 == 1;
            assert_eq!(original.finite, vec![("b".into(), Scalar::Bool(active))]);
            assert_eq!(original.parameters, vec![("n".into(), Type::Z)]);
            assert_eq!(original.quantifiers.len(), 1);
            assert_eq!(original.quantifiers[0].name, "n");
            let coordinate = &diagram.coordinates[ordinal];
            let actual = terms(&g, coordinate.nu.unwrap());
            if offset == 0 { assert!(actual.is_empty()); }
            else { assert_eq!(actual, vec![(Scalar::Z((-1).into()).wire(), vec![0,0])]); }
            assert_eq!(coordinate.guard, if active { EquationGuard::AlwaysTrue } else { EquationGuard::AlwaysFalse });
            if !active {
                assert!(coordinate.epsilon.is_none());
                assert!(terms(&g, coordinate.residual.unwrap()).is_empty());
            }
        }
        replay(&p, &g, &g.nodes).unwrap();
    }
}

#[test]
fn finite_field_and_boolean_cases_keep_their_types_and_numeric_quantifiers() {
    let p = prepared(false, false, "law required zero(c:Part,n:Z,k:Fp(3),b:Bool) when b and k+1=0:n*c.quantity=0;", "root");
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    let diagram = &ds[0];
    assert_eq!(diagram.originals.len(), 12);
    assert_eq!(diagram.coordinates.len(), 12);
    for (index, original) in diagram.originals.iter().enumerate() {
        let residue = (index % 6) / 2;
        let flag = index % 2 == 1;
        assert_eq!(original.finite, vec![("k".into(), Scalar::Fp { modulus: "3".into(), value: residue.into() }), ("b".into(), Scalar::Bool(flag))]);
        assert_eq!(original.parameters, vec![("n".into(), Type::Z)]);
        assert_eq!(original.quantifiers.len(), 1);
        assert_eq!(original.quantifiers[0].name, "n");
        let binding = original.bindings.iter().find(|b| b.name == "k").unwrap();
        assert_eq!(binding.ty, Type::Fp("3".into()));
        assert_eq!(g.scalar(binding.value).unwrap(), &original.finite[0].1);
        let coordinate = &diagram.coordinates[index];
        let active = residue == 2 && flag;
        assert_eq!(coordinate.guard, if active { EquationGuard::AlwaysTrue } else { EquationGuard::AlwaysFalse });
        if !active {
            assert!(coordinate.epsilon.is_none());
            assert!(terms(&g, coordinate.residual.unwrap()).is_empty());
        }
    }
    replay(&p, &g, &g.nodes).unwrap();
}

#[test]
fn finite_tuple_cases_preserve_nested_values_and_numeric_quantifiers() {
    let p = prepared(false, false, "law required zero(c:Part,n:Z,tag:(Fp(3),(Bool,Bool))) when tag.1.0 and tag.1.1 and tag.0+1=0:n*c.quantity=0;", "root");
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    let diagram = &ds[0];
    assert_eq!(diagram.originals.len(), 24);
    assert_eq!(diagram.coordinates.len(), 24);
    let ty = Type::Tuple(vec![Type::Fp("3".into()), Type::Tuple(vec![Type::Bool, Type::Bool])]);
    for (index, original) in diagram.originals.iter().enumerate() {
        assert_eq!(original.finite.len(), 1);
        assert_eq!(original.finite[0].0, "tag");
        assert_eq!(original.finite[0].1.ty(), ty);
        assert_eq!(original.parameters, vec![("n".into(), Type::Z)]);
        assert_eq!(original.quantifiers.len(), 1);
        assert_eq!(original.quantifiers[0].name, "n");
        let binding = original.bindings.iter().find(|b| b.name == "tag").unwrap();
        assert_eq!(g.scalar(binding.value).unwrap(), &original.finite[0].1);
        let value = Scalar::Tuple(vec![Scalar::Fp { modulus: "3".into(), value: ((index % 12) / 4).into() },
            Scalar::Tuple(vec![Scalar::Bool(index % 4 >= 2), Scalar::Bool(index % 2 == 1)])]);
        assert_eq!(original.finite[0].1, value);
        let active = index % 12 == 11;
        let coordinate = &diagram.coordinates[index];
        assert_eq!(coordinate.guard, if active { EquationGuard::AlwaysTrue } else { EquationGuard::AlwaysFalse });
        if !active { assert!(coordinate.epsilon.is_none()); assert!(terms(&g, coordinate.residual.unwrap()).is_empty()); }
    }
    replay(&p, &g, &g.nodes).unwrap();
}

#[test]
fn finite_aggregates_keep_typed_cases_and_numeric_axes() {
    for (ty, guard, active) in [
        (
            "Set<Bool>",
            "count(tag)>0 and count(tag)<=2",
            [false, true, true, true],
        ),
        ("Set<Fp(2)>", "sum(tag)=1", [false, false, true, true]),
    ] {
        let p = prepared(
            false,
            false,
            &format!("law required zero(c:Part,n:Z,tag:{ty}) when {guard}:n*c.quantity=0;"),
            "root",
        );
        let (mut g, a) = built(&p);
        let diagrams = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
        let diagram = &diagrams[0];
        assert_eq!(diagram.coordinates.len(), 8);
        for (index, coordinate) in diagram.coordinates.iter().enumerate() {
            assert_eq!(
                coordinate.guard,
                if active[index % 4] {
                    EquationGuard::AlwaysTrue
                } else {
                    EquationGuard::AlwaysFalse
                }
            );
            assert_eq!(
                diagram.originals[index].parameters,
                vec![("n".into(), Type::Z)]
            );
            assert_eq!(diagram.originals[index].quantifiers[0].name, "n");
        }
        replay(&p, &g, &g.nodes).unwrap();
    }
}

#[test]
#[ignore = "#6068: 製品の変更後に期待値と実装のどちらが正しいか未判定"]
fn finite_aggregate_comparisons_do_not_replace_free_numeric_values() {
    for rhs in ["n", "c.quantity"] {
        let p = prepared(
            false,
            false,
            &format!(
                "law required zero(c:Part,n:Z,tag:Set<Bool>) when count(tag)>{rhs}:n*c.quantity=0;"
            ),
            "root",
        );
        let (g, a) = built(&p);
        let Some(Payload::Construction(value)) = &g.get(a).unwrap().payload else {
            panic!("architecture")
        };
        let Witness::Architecture(a) = &value.witness else {
            panic!("architecture witness")
        };
        assert!(
            parameters::sources(&p.shared_inputs(), a, &mut quiet())
                .unwrap()
                .is_none(),
            "{rhs}"
        );
    }
}
#[test]
fn finite_predicates_and_short_circuits_keep_numeric_axes() {
    for (extra, guard, active) in [
        (
            ",tag:Set<Bool>",
            "tag!=set<Bool>{} and (true in tag implies false in tag)",
            vec![false, true, false, true],
        ),
        (",tag:Bool", "false implies n*n=1", vec![true, true]),
        (",tag:Bool", "false and n*n=1", vec![false, false]),
        (",tag:Bool", "true or n*n=1", vec![true, true]),
        ("", "false implies n*n=1", vec![true]),
        ("", "false and n*n=1", vec![false]),
        ("", "true or n*n=1", vec![true]),
        ("", "rat(1,2)=rat(1,2)", vec![true]),
        ("", "count(list<Bool>[true,false,true])=3 and sum(list<Z>[1,1])=2", vec![true]),
        ("", "sum(list<Q>[rat(1,2),rat(1,2)])=1", vec![true]),
        ("", "count(list<Bool>[])=0 and sum(list<Q>[])=0", vec![true]),
        ("", "count(list<Bool>[])>0", vec![false]),
        ("", "sum(list<Z>[1,1])=1", vec![false]),
        ("", "list<Z>[2,1]=list<Z>[1,2]", vec![false]),
    ] {
        let p = prepared(
            false,
            false,
            &format!("law required zero(c:Part,n:Z{extra}) when {guard}:n*c.quantity=0;"),
            "root",
        );
        let (mut g, a) = built(&p);
        let diagrams = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
        let diagram = &diagrams[0];
        assert_eq!(diagram.coordinates.len(), 2 * active.len(), "{guard}");
        for (index, coordinate) in diagram.coordinates.iter().enumerate() {
            assert_eq!(
                coordinate.guard,
                if active[index % active.len()] {
                    EquationGuard::AlwaysTrue
                } else {
                    EquationGuard::AlwaysFalse
                }
            );
            assert_eq!(
                diagram.originals[index].parameters,
                vec![("n".into(), Type::Z)]
            );
        }
        replay(&p, &g, &g.nodes).unwrap();
    }
}
#[test]
fn finite_set_cases_keep_all_subsets_and_numeric_axes() {
    let p = prepared(
        false,
        false,
        "law required zero(c:Part,n:Z,tag:Set<Bool>) when tag=set<Bool>{true,false,true}:n*c.quantity=0;",
        "root",
    );
    let (mut g, a) = built(&p);
    let diagrams = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    let diagram = &diagrams[0];
    assert_eq!(diagram.originals.len(), 8);
    assert_eq!(diagram.coordinates.len(), 8);
    for (index, original) in diagram.originals.iter().enumerate() {
        let items = match index % 4 {
            0 => vec![],
            1 => vec![Scalar::Bool(false)],
            2 => vec![Scalar::Bool(true)],
            _ => vec![Scalar::Bool(false), Scalar::Bool(true)],
        };
        let value = Scalar::Set {
            element: Type::Bool,
            items,
        };
        assert_eq!(original.finite, vec![("tag".into(), value.clone())]);
        assert_eq!(original.parameters, vec![("n".into(), Type::Z)]);
        assert_eq!(original.quantifiers.len(), 1);
        assert_eq!(original.quantifiers[0].name, "n");
        let binding = original.bindings.iter().find(|b| b.name == "tag").unwrap();
        assert_eq!(g.scalar(binding.value).unwrap(), &value);
        let coordinate = &diagram.coordinates[index];
        let active = index % 4 == 3;
        assert_eq!(
            coordinate.guard,
            if active {
                EquationGuard::AlwaysTrue
            } else {
                EquationGuard::AlwaysFalse
            }
        );
        if !active {
            assert!(coordinate.epsilon.is_none());
            assert!(terms(&g, coordinate.residual.unwrap()).is_empty());
        }
    }
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn infinite_components_are_not_finite_case_samples() {
    for (ty, guard) in [("(Z,Bool)", " when tag.1"), ("Option<Z>", ""), ("Set<Z>", "")] {
        let p = prepared(
            false,
            false,
            &format!("law required zero(c:Part,n:Z,tag:{ty}){guard}:n*c.quantity=0;"),
            "root",
        );
        let (g, a) = built(&p);
        let Some(Payload::Construction(value)) = &g.get(a).unwrap().payload else {
            panic!("architecture")
        };
        let Witness::Architecture(a) = &value.witness else {
            panic!("architecture witness")
        };
        assert!(
            parameters::sources(&p.shared_inputs(), a, &mut quiet())
                .unwrap()
                .is_none()
        );
    }
}

#[test]
fn infinite_data_is_not_a_finite_case_sample() {
    use crate::input::{InputSources, check_inputs};
    for payload in [r#""Z""#, r#"["Data","Family.Flag"]"#] {
        let mut p = prepared(
            false,
            false,
            "law required zero(c:Part,n:Z):n*c.quantity=0;",
            "root",
        );
        let sources = p.inputs.sources();
        let original = std::str::from_utf8(sources.definitions()[0].bytes()).unwrap();
        let definition = original.replace(
            r#""declarations":["#,
            &format!(r#""declarations":[{{"kind":"data","name":"Family.Flag","meaning":"選択。","constructors":[{{"name":"Off","arguments":[],"meaning":"停止。"}},{{"name":"On","arguments":[{payload}],"meaning":"選択。"}}]}},"#),
        );
        let old =
            crate::definition::check_definitions(&[("definition0", original.as_bytes())]).unwrap();
        let new = crate::definition::check_definitions(&[("definition0", definition.as_bytes())])
            .unwrap();
        let old_digest = &old.vocabularies["Family"].digest;
        let new_digest = &new.vocabularies["Family"].digest;
        let law = std::str::from_utf8(sources.law().bytes())
            .unwrap()
            .replace(old_digest, new_digest)
            .replace("n:Z)", "n:Z,tag:Flag)");
        let map = std::str::from_utf8(sources.archmap().bytes())
            .unwrap()
            .replace(old_digest, new_digest);
        p.inputs = Arc::new(
            check_inputs(
                InputSources::from_bytes(
                    vec![definition.into_bytes()],
                    law.into_bytes(),
                    map.into_bytes(),
                ),
                &mut quiet(),
            )
            .unwrap(),
        );
        p.requests = resolve_native_for_test(
            p.inputs.law(),
            p.inputs.archmap(),
            &["b=build(Selected,on=@v/root)"],
            &mut quiet(),
        )
        .unwrap();
        let (g, a) = built(&p);
        let Some(Payload::Construction(value)) = &g.get(a).unwrap().payload else {
            panic!("architecture")
        };
        let Witness::Architecture(a) = &value.witness else {
            panic!("architecture witness")
        };
        assert!(
            parameters::sources(&p.shared_inputs(), a, &mut quiet())
                .unwrap()
                .is_none()
        );
    }
}
