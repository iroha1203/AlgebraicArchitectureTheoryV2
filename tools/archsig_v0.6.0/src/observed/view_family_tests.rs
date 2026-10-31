use super::*;
use crate::{
    control::{Limits, Usage},
    input::InputSources,
    observed::{PreparedObserved, request::resolve_native_for_test},
};
use std::sync::Arc;
const DEFINITION: &[u8] = include_bytes!("../../tests/fixtures/configuration-profile.atoms.json");
const LAW: &str = include_str!("../../tests/fixtures/configuration-profile.law");
const MAP: &str = include_str!("../../tests/fixtures/configuration-profile.archmap.json");
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn prepared(law: &str, map: &str) -> PreparedObserved {
    let definitions = crate::definition::check_definitions(&[("definition0", DEFINITION)]).unwrap();
    let digest = &definitions.vocabularies["Profile"].digest;
    let inputs = Arc::new(
        crate::input::check_inputs(
            InputSources::from_bytes(
                vec![DEFINITION.to_vec()],
                law.replace("@PROFILE_DIGEST@", digest).into_bytes(),
                map.replace("@PROFILE_DIGEST@", digest).into_bytes(),
            ),
            &mut quiet(),
        )
        .unwrap(),
    );
    let requests = resolve_native_for_test(
        inputs.law(),
        inputs.archmap(),
        &["b=build(ProfileRead,on=@v/A)"],
        &mut quiet(),
    )
    .unwrap();
    PreparedObserved {
        inputs,
        requests,
        object: None,
    }
}
fn start(p: &PreparedObserved) -> (Graph, super::super::object_component_diagram::Diagram) {
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
    (g, objects)
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
        let checked = env.validate(&prefix, n);
        assert!(checked.is_ok(), "node {i}: {checked:?}");
        prefix.push(n.clone()).unwrap();
    }
}
fn selected(
    g: &Graph,
    o: &super::super::object_component_diagram::Diagram,
    object: usize,
    name: &str,
) -> NodeRef {
    o.readings
        .iter()
        .find(|r| {
            r.object == object
                && reading::origin(g, r.expression)
                    .unwrap()
                    .1
                    .declaration
                    .ends_with(name)
        })
        .unwrap()
        .expression
}
#[test]
fn two_boolean_parameters_keep_all_four_rows_and_actual_option_values() {
    let law = LAW.replace(
        "view root(r: Root): Bool = true;",
        "view adjusted(p:Part,a:Bool,b:Bool):Z=amount(p)+(if a then 1 else 0)+(if b then 1 else 0);",
    );
    let p = prepared(&law, MAP);
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    // 対象ごとの族は同じ経路を通るので、最初の対象を代表にする。
    let expression = selected(&g, &o, 0, ".adjusted");
    let Outcome::Family(f) = evaluate(&env, &mut g, expression, &mut quiet()).unwrap() else {
        panic!()
    };
    assert_eq!(f.domains.len(), 2);
    assert_eq!(f.expressions.len(), 4);
    for r in &f.expressions {
        let n = g.get(*r).unwrap();
        assert!(n.arguments.contains(&f.product));
        assert!(f.domains.iter().all(|d| n.arguments.contains(d)));
    }
    assert_eq!(f.evaluations.len(), 4);
    let mut values = vec![];
    for e in &f.evaluations {
        let Some(Payload::Evaluation { value: Some(v), .. }) = &g.get(*e).unwrap().payload else {
            panic!()
        };
        values.push(g.scalar(*v).unwrap().clone());
    }
    assert_eq!(
        values,
        [2, 3, 3, 4]
            .into_iter()
            .map(|v| Scalar::Option {
                element: Type::Z,
                value: Some(Box::new(Scalar::Z(v.into())))
            })
            .collect::<Vec<_>>()
    );
    let Some(Payload::Evaluation {
        expression: r,
        value,
        parts,
        ..
    }) = &g.get(f.evaluation).unwrap().payload
    else {
        panic!()
    };
    assert_eq!(*r, expression);
    assert!(value.is_none());
    assert_eq!(parts[0].children, f.evaluations);
    assert_eq!(
        g.get(f.evaluation)
            .unwrap()
            .scope
            .quantifiers
            .iter()
            .map(|q| q.name.as_str())
            .collect::<Vec<_>>(),
        vec!["a", "b"]
    );
}
#[test]
fn composite_option_bool_and_set_bool_use_complete_domains() {
    let law=LAW.replace("view root(r: Root): Bool = true;","view choose(p:Part,x:Option<Bool>,b:Bool):Option<Bool> = x; view size(p:Part,x:Set<Bool>):Z=count(x);");
    let p = prepared(&law, MAP);
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let expression = selected(&g, &o, 0, ".choose");
    let Outcome::Family(f) = evaluate(&env, &mut g, expression, &mut quiet()).unwrap() else {
        panic!()
    };
    assert_eq!(f.expressions.len(), 6);
    let expected = [None, None, Some(false), Some(false), Some(true), Some(true)];
    for (e, expected) in f.evaluations.iter().zip(expected) {
        let Some(Payload::Evaluation { value: Some(v), .. }) = &g.get(*e).unwrap().payload else {
            panic!()
        };
        assert_eq!(
            g.scalar(*v).unwrap(),
            &Scalar::Option {
                element: Type::Option(Box::new(Type::Bool)),
                value: Some(Box::new(Scalar::Option {
                    element: Type::Bool,
                    value: expected.map(|x| Box::new(Scalar::Bool(x)))
                }))
            }
        );
    }
    let expression = selected(&g, &o, 0, ".size");
    let Outcome::Family(f) = evaluate(&env, &mut g, expression, &mut quiet()).unwrap() else {
        panic!()
    };
    assert_eq!(f.evaluations.len(), 4);
    let mut values = vec![];
    for e in f.evaluations {
        let Some(Payload::Evaluation { value: Some(v), .. }) = &g.get(e).unwrap().payload else {
            panic!()
        };
        values.push(g.scalar(*v).unwrap().clone());
    }
    assert_eq!(
        values,
        [0, 1, 1, 2]
            .into_iter()
            .map(|n| Scalar::Option {
                element: Type::Z,
                value: Some(Box::new(Scalar::Z(n.into())))
            })
            .collect::<Vec<_>>()
    );
    replay(&p, &g);
}
#[test]
fn empty_roster_product_is_empty_but_list_of_empty_roster_has_one_value() {
    let law=LAW.replace("view root(r: Root): Bool = true;","view vacant(p:Part,x:(External,Bool)):Z=amount(p); view emptyList(p:Part,x:List<External>):Z=count(x)+amount(p);");
    let map = MAP
        .lines()
        .filter(|l| !l.contains("\"id\":\"x\"") && !l.contains("\"id\":\"x-quantity\""))
        .collect::<Vec<_>>()
        .join("\n");
    // xはそれぞれの配列末尾なので、直前のcommaも独立に除く。
    let map = map.replace("\"origin\":\"model\"},\n]", "\"origin\":\"model\"}\n]");
    let p = prepared(&law, &map);
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let expression = selected(&g, &o, 0, ".vacant");
    let before = g.instances.len();
    let Outcome::Family(f) = evaluate(&env, &mut g, expression, &mut quiet()).unwrap() else {
        panic!()
    };
    assert!(f.expressions.is_empty() && f.evaluations.is_empty());
    assert_eq!(g.instances.len(), before);
    assert_eq!(g.get(f.product).unwrap().ty, NodeType::Domain);
    let Some(Payload::Construction(v)) = &g.get(f.product).unwrap().payload else {
        panic!()
    };
    assert_eq!(
        v.wire(),
        Json::obj([
            ("kind", Json::str("finite")),
            (
                "type",
                Type::Tuple(vec![Type::Ref("Profile.External".into()), Type::Bool]).wire()
            ),
            ("elements", Json::Arr(vec![]))
        ])
    );
    let expression = selected(&g, &o, 0, ".emptyList");
    let Outcome::Family(f) = evaluate(&env, &mut g, expression, &mut quiet()).unwrap() else {
        panic!()
    };
    assert_eq!(f.evaluations.len(), 1);
    let Some(Payload::Evaluation { value: Some(v), .. }) =
        &g.get(f.evaluations[0]).unwrap().payload
    else {
        panic!()
    };
    assert_eq!(
        g.scalar(*v).unwrap(),
        &Scalar::Option {
            element: Type::Z,
            value: Some(Box::new(Scalar::Z(2.into())))
        }
    );
    replay(&p, &g);
}
fn family(env: &Environment<'_>, g: &mut Graph, r: NodeRef) -> Family {
    let Outcome::Family(f) = evaluate(env, g, r, &mut quiet()).unwrap() else {
        panic!()
    };
    f
}
#[test]
fn fp_rows_and_missing_body_keep_real_values_and_original_missing_slots() {
    let law=LAW.replace("view root(r: Root): Bool = true;","view residue(p:Part,n:Fp(2)):Fp(2)=n; view shifted(p:Part,b:Bool):Z=amount(p)+(if b then 1 else 0);");
    for missing in [false, true] {
        let map = if missing {
            MAP.lines()
                .filter(|l| !l.contains("\"id\":\"p-quantity\""))
                .collect::<Vec<_>>()
                .join("\n")
        } else {
            MAP.into()
        };
        let p = prepared(&law, &map);
        let (mut g, o) = start(&p);
        let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
        let r = selected(&g, &o, 0, ".residue");
        let f = family(&env, &mut g, r);
        assert_eq!(f.evaluations.len(), 2);
        for (i, e) in f.evaluations.iter().enumerate() {
            let Some(Payload::Evaluation { value: Some(v), .. }) = &g.get(*e).unwrap().payload
            else {
                panic!()
            };
            assert_eq!(
                g.scalar(*v).unwrap(),
                &Scalar::Option {
                    element: Type::Fp("2".into()),
                    value: Some(Box::new(Scalar::Fp {
                        modulus: "2".into(),
                        value: i.into()
                    }))
                }
            );
        }
        let r = selected(&g, &o, 0, ".shifted");
        let f = family(&env, &mut g, r);
        assert_eq!(f.evaluations.len(), 2);
        for (i, e) in f.evaluations.iter().enumerate() {
            let Some(Payload::Evaluation { value, parts, .. }) = &g.get(*e).unwrap().payload else {
                panic!()
            };
            if missing {
                assert!(value.is_none());
                assert_eq!(parts[0].children.len(), 1);
                assert!(
                    g.get(*e)
                        .unwrap()
                        .reasons
                        .iter()
                        .flat_map(|r| &r.missing)
                        .any(|f| f.subject == "p"
                            && f.field.as_deref() == Some("Profile.Part.quantity"))
                );
            } else {
                assert_eq!(
                    g.scalar(value.unwrap()).unwrap(),
                    &Scalar::Option {
                        element: Type::Z,
                        value: Some(Box::new(Scalar::Z((i + 2).into())))
                    }
                );
            }
        }
        assert_eq!(g.get(f.evaluation).unwrap().reasons.is_empty(), !missing);
        replay(&p, &g);
    }
}
fn external_prepared(extra: &str) -> PreparedObserved {
    let left = include_bytes!("../../tests/fixtures/object-view-transport.atoms.json");
    let right = include_bytes!("../../tests/fixtures/configuration-map-right.atoms.json");
    let defs = crate::definition::check_definitions(&[("left", left), ("right", right)]).unwrap();
    let ld = &defs.vocabularies["Left"].digest;
    let rd = &defs.vocabularies["Right"].digest;
    let bridge = include_str!("../../tests/fixtures/configuration-map-bridge.atoms.json")
        .replace("@LEFT_DIGEST@", ld)
        .replace("@RIGHT_DIGEST@", rd);
    let defs = crate::definition::check_definitions(&[
        ("left", left),
        ("right", right),
        ("bridge", bridge.as_bytes()),
    ])
    .unwrap();
    let expand = |s: &str| {
        s.replace("@LEFT_DIGEST@", ld)
            .replace("@RIGHT_DIGEST@", rd)
            .replace("@BRIDGE_DIGEST@", &defs.vocabularies["Bridge"].digest)
            .into_bytes()
    };
    let law = include_str!("../../tests/fixtures/object-view-transport.law").replacen(
        "  view amount(c:",
        &format!("{extra}\n  view amount(c:"),
        1,
    );
    let inputs = Arc::new(
        crate::input::check_inputs(
            InputSources::from_bytes(
                vec![left.to_vec(), right.to_vec(), bridge.into_bytes()],
                expand(&law),
                expand(include_str!(
                    "../../tests/fixtures/object-view-transport.archmap.json"
                )),
            ),
            &mut quiet(),
        )
        .unwrap(),
    );
    let requests = resolve_native_for_test(
        inputs.law(),
        inputs.archmap(),
        &["b=build(Before,on=@v/a)"],
        &mut quiet(),
    )
    .unwrap();
    PreparedObserved {
        inputs,
        requests,
        object: None,
    }
}
#[test]
fn nonnumeric_and_missing_owned_domains_preserve_the_whole_signature_without_fake_rows() {
    let law=LAW.replace("view root(r: Root): Bool = true;","view shift(p:Part,n:Text,b:Bool):Z=amount(p); view owned(r:Root,x:Option<Part[r]>,b:Bool):Bool=true;");
    let p = prepared(&law, MAP);
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let r = selected(&g, &o, 0, ".shift");
    let before = copy(&g, &quiet());
    let Outcome::Pending(pending) = evaluate(&env, &mut g, r, &mut quiet()).unwrap() else {
        panic!()
    };
    assert_eq!(pending.expression, r);
    assert_eq!(
        pending
            .parameters
            .iter()
            .map(|p| p.declaration.name.as_str())
            .collect::<Vec<_>>(),
        vec!["n", "b"]
    );
    assert!(pending.parameters[0].values.is_none());
    assert!(pending.parameters[0].missing.is_empty());
    assert_eq!(
        pending.parameters[1].values.as_ref().unwrap(),
        &vec![Scalar::Bool(false), Scalar::Bool(true)]
    );
    assert_eq!(g.nodes, before.nodes);
    assert_eq!(g.contexts, before.contexts);
    assert_eq!(g.instances, before.instances);
    assert_eq!(g.active, before.active);
    let r = selected(&g, &o, 0, ".owned");
    let f = family(&env, &mut g, r);
    assert_eq!(f.evaluations.len(), 4);
    assert_eq!(
        g.get(f.evaluation)
            .unwrap()
            .scope
            .quantifiers
            .iter()
            .map(|q| q.ty.clone())
            .collect::<Vec<_>>(),
        vec![
            Type::Option(Box::new(Type::Ref("Profile.Part".into()))),
            Type::Bool
        ]
    );
    replay(&p, &g);
    // 局所対象族を未完成にしない外部ownerの欠測で、値域そのものの保留を検証する。
    let p = external_prepared(
        "view ownershipProbe(c:Left.Child,a:Left.ExternalRoot,x:Option<Left.ExternalChild[a]>,b:Bool):Bool=true;",
    );
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut count = 0;
    for row in &o.readings {
        if row.object != 0
            || !reading::origin(&g, row.expression)
                .unwrap()
                .1
                .declaration
                .ends_with(".ownershipProbe")
        {
            continue;
        }
        let before = copy(&g, &quiet());
        let Outcome::Pending(pending) =
            evaluate(&env, &mut g, row.expression, &mut quiet()).unwrap()
        else {
            panic!()
        };
        assert_eq!(pending.expression, row.expression);
        assert_eq!(
            pending.parameters[0].declaration.ty,
            Type::Option(Box::new(Type::Owned(
                "Left.ExternalChild".into(),
                "a".into()
            )))
        );
        assert!(pending.parameters[0].missing.iter().any(|f|f.subject=="y"&&f.field.as_deref()==Some("Left.ExternalChild.owner")));
        assert!(pending.parameters[0].values.as_ref().unwrap().len() >= 1);
        assert_eq!(pending.parameters[1].values.as_ref().unwrap().len(), 2);
        assert_eq!(g.nodes, before.nodes);
        assert_eq!(g.contexts, before.contexts);
        assert_eq!(g.instances, before.instances);
        assert_eq!(g.active, before.active);
        count += 1;
    }
    assert!(count > 0);
    replay(&p, &g);
}
#[test]
fn mixed_numeric_rows_retain_all_numeric_parameters_and_finite_choices() {
    for (ty, tuple) in [("Q", false), ("Z", true)] {
        let parameter_ty = if tuple { format!("({ty},({ty},{ty}))") } else { ty.to_owned() };
        let term = if tuple { "n.0+n.1.1" } else { "n" };
        let offset = if ty == "Z" { "amount(p)" } else { "rat(1,2)" };
        let law = LAW.replace("view root(r: Root): Bool = true;", &format!(
            "view shift(p:Part,n:{parameter_ty},b:Bool,m:{ty}):{ty}=if b then {term}+m+{offset} else {term}+m;"));
        let p = prepared(&law, MAP);
        let (mut g, o) = start(&p);
        let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
        let r = selected(&g, &o, 0, ".shift");
        let f = family(&env, &mut g, r);
        assert_eq!(f.domains.len(), 1);
        assert_eq!(f.evaluations.len(), 2);
        for (index, expression) in f.expressions.iter().enumerate() {
            let (_, origin) = reading::origin(&g, *expression).unwrap();
            assert_eq!(origin.parameters.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>(), ["n", "m"]);
            let coefficient = if ty == "Z" { Type::Z } else { Type::Q };
            let expected = if tuple { Type::Tuple(vec![coefficient.clone(), Type::Tuple(vec![coefficient.clone(), coefficient.clone()])]) } else { coefficient.clone() };
            assert_eq!(origin.parameters[0].1, expected);
            assert_eq!(origin.parameters[1].1, coefficient);
            assert_eq!(g.scalar(origin.bindings.iter().find(|b| b.name == "b").unwrap().value).unwrap(), &Scalar::Bool(index == 1));
            assert!(matches!(&g.get(f.evaluations[index]).unwrap().payload, Some(Payload::Evaluation { value: None, .. })));
        }
        let mut bad = g.get(f.evaluation).unwrap().clone();
        let Some(Payload::Evaluation { parts, .. }) = &mut bad.payload else { panic!() };
        parts[0].children.reverse();
        assert!(validate_family(&g, &bad, f.evaluation.0).is_err());
        replay(&p, &g);
    }
}
#[test]
fn family_metadata_rejects_duplicated_quantifiers() {
    let law=LAW.replace("view root(r: Root): Bool = true;","view adjusted(p:Part,a:Bool,b:Bool):Z=amount(p)+(if a then 1 else 0)+(if b then 1 else 0);");
    let p = prepared(&law, MAP);
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let r = selected(&g, &o, 0, ".adjusted");
    let f = family(&env, &mut g, r);
    assert_eq!(g.get(f.evaluation).unwrap().scope.quantifiers.len(), 2);
    let mut bad = copy(&g, &quiet());
    let q = bad.nodes[f.evaluation.0].scope.quantifiers[0].clone();
    bad.nodes[f.evaluation.0].scope.quantifiers.push(q);
    let fresh = Environment::with_prepared(&p, &mut quiet()).unwrap();
    assert!(
        fresh
            .recheck_node(&bad, bad.get(f.evaluation).unwrap(), f.evaluation.0)
            .is_err()
    );
    replay(&p, &g);
}
#[test]
fn conditional_membership_keeps_all_bool_rows_without_evaluating_constant_true() {
    let p = external_prepared(
        "view conditionalProbe(c:Left.Child,a:Left.ExternalRoot,e:Left.ExternalChild[a],b:Bool):Bool=true;",
    );
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut count = 0;
    for row in &o.readings {
        let (_, origin) = reading::origin(&g, row.expression).unwrap();
        if row.object != 0
            || !origin.declaration.ends_with(".conditionalProbe")
            || !matches!(&origin.application,crate::construction::readings::InstanceApplication::Applicable{conditions} if !conditions.is_empty())
        {
            continue;
        }
        let before = g.instances.len();
        let f = family(&env, &mut g, row.expression);
        assert_eq!(f.evaluations.len(), 2);
        assert_eq!(g.instances.len(), before);
        for e in &f.evaluations {
            let Some(Payload::Evaluation {
                value,
                parts,
                applicability,
                ..
            }) = &g.get(*e).unwrap().payload
            else {
                panic!()
            };
            assert!(value.is_none());
            assert!(parts[0].children.is_empty());
            assert_eq!(*applicability, "undetermined");
            assert!(
                g.get(*e)
                    .unwrap()
                    .reasons
                    .iter()
                    .flat_map(|r| &r.missing)
                    .any(|f| f.subject == "y"
                        && f.field.as_deref() == Some("Left.ExternalChild.owner"))
            );
        }
        assert!(!g.get(f.evaluation).unwrap().reasons.is_empty());
        assert!(matches!(
            &g.get(f.evaluation).unwrap().payload,
            Some(Payload::Evaluation {
                applicability: "undetermined",
                ..
            })
        ));
        count += 1;
    }
    assert!(count > 0);
    replay(&p, &g);
}
#[test]
fn saved_family_domains_rows_and_evaluations_survive_a_later_request() {
    let law=LAW.replace("view root(r: Root): Bool = true;","view adjusted(p:Part,a:Bool,b:Bool):Z=amount(p)+(if a then 1 else 0)+(if b then 1 else 0);");
    let mut p = prepared(&law, MAP);
    p.requests = resolve_native_for_test(
        p.inputs.law(),
        p.inputs.archmap(),
        &[
            "b=build(ProfileRead,on=@v/A)",
            "later=build(ProfileRead,on=@v/B)",
        ],
        &mut quiet(),
    )
    .unwrap();
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let expression = selected(&g, &o, 0, ".adjusted");
    let start = g.nodes.len();
    let f = family(&env, &mut g, expression);
    let end = g.nodes.len();
    assert_eq!(f.expressions.len(), 4);
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
    let fresh = Environment::with_prepared(&p, &mut quiet()).unwrap();
    for at in start..end {
        let result = fresh.recheck_node(&g, g.get(NodeRef(at)).unwrap(), at);
        assert!(result.is_ok(), "node {at}: {result:?}");
    }
    let before = copy(&g, &quiet());
    assert!(evaluate(&env, &mut g, expression, &mut quiet()).is_err());
    assert_eq!(g.nodes, before.nodes);
    assert_eq!(g.contexts, before.contexts);
    assert_eq!(g.instances, before.instances);
    assert_eq!(g.active, before.active);
    for mode in 0..3 {
        let mut bad = copy(&g, &quiet());
        match mode {
            0 => bad.requests[0].id = "foreign".into(),
            1 => bad.contexts[f.evaluation.0].request = 1,
            2 => bad.contexts[f.domains[0].0].request = 1,
            _ => unreachable!(),
        };
        let fresh = Environment::with_prepared(&p, &mut quiet()).unwrap();
        assert!(
            fresh
                .recheck_node(&bad, bad.get(f.evaluation).unwrap(), f.evaluation.0)
                .is_err()
        );
    }
}
#[test]
fn interrupt_preserves_exact_completed_domain_row_and_evaluation_prefix() {
    use std::{
        cell::{Cell, RefCell},
        rc::Rc,
    };
    let law=LAW.replace("view root(r: Root): Bool = true;","view adjusted(p:Part,a:Bool,b:Bool):Z=amount(p)+(if a then 1 else 0)+(if b then 1 else 0);");
    let p = prepared(&law, MAP);
    let (initial, o) = start(&p);
    let expression = selected(&initial, &o, 0, ".adjusted");
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let native_points = Rc::new(RefCell::new(Vec::new()));
    let points = native_points.clone();
    let mut control = Control::new(Limits::default(), move |p| {
        seen.set(seen.get() + 1);
        if p == Checkpoint::NativeResultNode {
            points.borrow_mut().push(seen.get());
        }
        Usage::default()
    });
    let mut full = copy(&initial, &control);
    let Outcome::Family(f) = evaluate(&env, &mut full, expression, &mut control).unwrap() else {
        panic!()
    };
    assert_eq!(f.evaluations.len(), 4);
    let total = count.get();
    assert!(total > 10);
    assert!(native_points.borrow().len() > 2);
    let early = native_points.borrow()[1];
    let mut domain_prefix = false;
    let mut row_prefix = false;
    for at in [early, total / 2, total] {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let mut control = Control::new(Limits::default(), move |_| {
            seen.set(seen.get() + 1);
            let hit = seen.get() >= at;
            Usage {
                signal: hit.then_some(crate::result::Signal::Int),
                ..Usage::default()
            }
        });
        let mut g = copy(&initial, &control);
        let result = evaluate(&env, &mut g, expression, &mut control);
        assert!(
            matches!(result, Err(ValidationFailure::Stop(_))),
            "at{at}: {result:?}"
        );
        assert_eq!(g.active, initial.active);
        assert!(env.architecture_ref().is_none());
        assert!(g.nodes.len() <= full.nodes.len());
        for (i, n) in g.nodes.iter().enumerate() {
            assert_eq!(
                n.wire(i, &g.nodes[..i]),
                full.nodes[i].wire(i, &full.nodes[..i])
            );
        }
        assert_eq!(g.contexts, &full.contexts[..g.contexts.len()]);
        assert_eq!(g.instances, &full.instances[..g.instances.len()]);
        assert_eq!(g.frames, &full.frames[..g.frames.len()]);
        assert_eq!(g.iterations, &full.iterations[..g.iterations.len()]);
        assert_eq!(g.cases, &full.cases[..g.cases.len()]);
        domain_prefix |= g.nodes.len() > initial.nodes.len() && g.instances.is_empty();
        row_prefix |= !g.instances.is_empty();
        replay(&p, &g);
    }
    assert!(domain_prefix && row_prefix);
}
#[test]
fn an_inapplicable_view_family_keeps_every_none_and_never_runs_a_body() {
    let law = LAW.replace(
        "view root(r: Root): Bool = true;",
        "view root(r:Root,b:Bool):Bool=true;",
    );
    let p = prepared(&law, MAP);
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let r = selected(&g, &o, 1, ".root");
    let before = g.instances.len();
    let f = family(&env, &mut g, r);
    assert_eq!(f.evaluations.len(), 2);
    assert_eq!(g.instances.len(), before);
    for e in &f.evaluations {
        let Some(Payload::Evaluation {
            value: Some(v),
            parts,
            applicability,
            ..
        }) = &g.get(*e).unwrap().payload
        else {
            panic!()
        };
        assert_eq!(*applicability, "not_applicable");
        assert!(parts[0].children.is_empty());
        assert_eq!(
            g.scalar(*v).unwrap(),
            &Scalar::Option {
                element: Type::Bool,
                value: None
            }
        );
    }
    assert!(matches!(
        &g.get(f.evaluation).unwrap().payload,
        Some(Payload::Evaluation {
            applicability: "not_applicable",
            value: None,
            ..
        })
    ));
    assert!(g.get(f.evaluation).unwrap().reasons.is_empty());
    replay(&p, &g);
}
