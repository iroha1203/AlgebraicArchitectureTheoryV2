use super::*;
use crate::input::check_inputs;
mod fixture {
    use crate as archsig;
    include!("../../../../tests/common/finite_data_quotient.rs");
}
fn quiet() -> Control {
    Control::unlimited()
}
fn inputs(extra: &str) -> crate::input::CheckedInputs {
    check_inputs(fixture::sources(extra, ""), &mut quiet()).unwrap()
}
fn data(name: &str, args: Vec<Scalar>) -> Scalar {
    let (family, _) = name.rsplit_once('.').unwrap();
    Scalar::Data {
        family: family.into(),
        constructor: name.into(),
        args,
    }
}
#[test]
fn finite_data_gate_visits_every_constructor_and_keeps_cycle_state_local() {
    let i = inputs(
        r#"
{"kind":"data","name":"Pair.Bad","meaning":"別枝の参照。","constructors":[{"name":"End","meaning":"空。","arguments":[]},{"name":"Loop","meaning":"再帰。","arguments":[["Data","Pair.Bad"]]},{"name":"Hidden","meaning":"参照。","arguments":[["List",["Option",["Ref","Pair.State"]]]]}]},
{"kind":"data","name":"Pair.BadMap","meaning":"写像。","constructors":[{"name":"Wrap","meaning":"包む。","arguments":[["Map",["Ref","Pair.State"],["Ref","Pair.State"]]]}]},
{"kind":"data","name":"Pair.BadTerm","meaning":"関数。","constructors":[{"name":"Wrap","meaning":"包む。","arguments":[["Term",["Bool"],"Bool"]]}]}
"#,
    );
    for name in ["Pair.Token", "Pair.Other", "Pair.Packet", "Pair.Tree"] {
        assert!(exact_type(&Type::Data(name.into()), i.law(), &mut quiet()).unwrap());
    }
    for name in ["Pair.Bad", "Pair.BadMap", "Pair.BadTerm"] {
        let bad = Type::Data(name.into());
        for ty in [
            bad.clone(),
            Type::Option(Box::new(bad.clone())),
            Type::Tuple(vec![Type::Data("Pair.Tree".into()), bad.clone()]),
            Type::Tuple(vec![bad, Type::Data("Pair.Tree".into())]),
        ] {
            assert!(!exact_type(&ty, i.law(), &mut quiet()).unwrap(), "{ty:?}");
        }
    }
    for ty in [
        Type::Ref("Pair.State".into()),
        Type::Owned("Pair.State".into(), "owner".into()),
        Type::Path("Pair.State".into(), "Pair.State".into()),
        Type::Map(Box::new(Type::Bool), Box::new(Type::Bool)),
        Type::Term(vec![Type::Bool], Box::new(Type::Bool)),
    ] {
        assert!(!exact_type(&Type::List(Box::new(ty)), i.law(), &mut quiet()).unwrap());
    }
    assert!(exact_type(&Type::Data("Pair.Tree".into()), i.law(), &mut quiet()).unwrap());
    assert!(exact_type(&Type::Data("Pair.Unknown".into()), i.law(), &mut quiet()).is_err());
}
#[test]
fn finite_data_values_validate_names_arity_payload_and_family_before_equality() {
    let i = inputs("");
    let left = data("Pair.Token.Left", vec![Scalar::Bool(false)]);
    let right = data("Pair.Token.Right", vec![Scalar::Bool(false)]);
    let empty = data("Pair.Token.Empty", vec![]);
    for value in [&left, &right, &empty] {
        data::check(value, i.law(), &quiet()).unwrap();
    }
    assert!(data::equal(&empty, &data("Pair.Token.Empty", vec![]), &quiet()).unwrap());
    assert!(!data::equal(&left, &right, &quiet()).unwrap());
    assert!(
        !data::equal(
            &left,
            &data("Pair.Token.Left", vec![Scalar::Bool(true)]),
            &quiet()
        )
        .unwrap()
    );
    assert!(
        !data::equal(
            &data(
                "Pair.Token.Both",
                vec![Scalar::Bool(false), Scalar::Bool(true)]
            ),
            &data(
                "Pair.Token.Both",
                vec![Scalar::Bool(true), Scalar::Bool(false)]
            ),
            &quiet()
        )
        .unwrap()
    );
    let other = data("Pair.Other.Left", vec![Scalar::Bool(false)]);
    data::check(&other, i.law(), &quiet()).unwrap();
    assert!(data::equal(&left, &other, &quiet()).is_err());
    for value in [
        data("Pair.Token.Missing", vec![]),
        data("Pair.Token.Left", vec![]),
        data("Pair.Token.Left", vec![Scalar::Z(0.into())]),
        data("Pair.Token.Empty", vec![Scalar::Bool(false)]),
        Scalar::Data {
            family: "Pair.Token".into(),
            constructor: "Pair.Other.Left".into(),
            args: vec![Scalar::Bool(false)],
        },
    ] {
        assert!(data::check(&value, i.law(), &quiet()).is_err(), "{value:?}");
    }
}

#[test]
fn finite_data_type_and_payload_traversals_keep_exact_stop_reasons() {
    use crate::control::StopReason;
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    let i = inputs("");
    let tree = data(
        "Pair.Tree.Branch",
        vec![
            data("Pair.Tree.Leaf", vec![Scalar::Bool(false)]),
            data("Pair.Tree.End", vec![]),
        ],
    );
    data::check(&tree, i.law(), &quiet()).unwrap();
    assert!(data::equal(&tree, &tree, &quiet()).unwrap());
    for type_walk in [true, false] {
        for signal in [Signal::Int, Signal::Term] {
            let count = Rc::new(Cell::new(0));
            let seen = count.clone();
            let target = if type_walk { 8 } else { 3 };
            let mut c = Control::new(move |point| {
                if point
                    == if type_walk {
                        Checkpoint::PrimitiveValuation
                    } else {
                        Checkpoint::FiniteIteration
                    }
                {
                    seen.set(seen.get() + 1);
                }
                (seen.get() == target).then_some(signal)
            });
            let result = if type_walk {
                exact_type(&Type::Data("Pair.Tree".into()), i.law(), &mut c)
            } else {
                data::equal(&tree, &tree, &c)
            };
            let expected = StopReason::Cancelled(signal);
            assert!(matches!(result,Err(ValidationFailure::Stop(reason)) if reason==expected));
            assert_eq!(count.get(), target);
        }
    }
}

#[test]
fn quantified_observation_requires_recorded_complete_finite_bindings() {
    let i = check_inputs(
        fixture::sources("", "law optional finite(s:State):forall b:Bool . b;"),
        &mut quiet(),
    )
    .unwrap();
    let Signature::Law { body, .. } = i.law().declarations["Pair.finite"].signature else {
        panic!("law")
    };
    let mut nodes = vec![EvaluationNode {
        expression: body,
        bindings: vec![],
        value: Some(Scalar::Bool(true)),
        residual: None,
        scope: Scope::default(),
        children: vec![],
        finite_bindings: None,
    }];
    assert!(
        observation(i.law(), body, Some(0), &nodes, &mut quiet())
            .unwrap()
            .1
            .is_none()
    );
    nodes[0].finite_bindings = Some(vec![Scalar::Bool(false), Scalar::Bool(true)]);
    assert!(
        observation(i.law(), body, Some(0), &nodes, &mut quiet())
            .unwrap()
            .1
            .is_none()
    );
    nodes[0].finite_bindings = Some(vec![]);
    assert!(
        matches!(observation(i.law(),body,Some(0),&nodes,&mut quiet()).unwrap().1,Some(Scalar::Set { ref items,.. }) if items.is_empty())
    );
}

#[test]
fn match_observation_rejects_wrong_pattern_binding_and_extra_arm_capture() {
    let i = check_inputs(
        fixture::sources(
            "",
            "law optional matched(s:State):match Token.Left(true) {Left(v)=>v=v;_=>true;};",
        ),
        &mut quiet(),
    )
    .unwrap();
    let Signature::Law { body, .. } = i.law().declarations["Pair.matched"].signature else {
        panic!("law")
    };
    let ExprKind::Match {
        scrutinee,
        ref arms,
    } = i.law().exprs[body].kind
    else {
        panic!("match")
    };
    let ExprKind::Binary { lhs, rhs, .. } = i.law().exprs[arms[0].body].kind else {
        panic!("eq")
    };
    let node = |expression, value, children, bindings| EvaluationNode {
        expression,
        value: Some(value),
        children,
        bindings,
        residual: None,
        scope: Scope::default(),
        finite_bindings: None,
    };
    let mut nodes = vec![
        node(
            scrutinee,
            data("Pair.Token.Left", vec![Scalar::Bool(true)]),
            vec![],
            vec![],
        ),
        node(lhs, Scalar::Bool(true), vec![], vec![]),
        node(rhs, Scalar::Bool(true), vec![], vec![]),
        node(
            arms[0].body,
            Scalar::Bool(true),
            vec![1, 2],
            vec![("v".into(), Scalar::Bool(false))],
        ),
        node(body, Scalar::Bool(true), vec![0, 3], vec![]),
    ];
    assert!(
        observation(i.law(), body, Some(4), &nodes, &mut quiet())
            .unwrap()
            .1
            .is_none()
    );
    nodes[3].bindings[0].1 = Scalar::Bool(true);
    assert!(
        observation(i.law(), body, Some(4), &nodes, &mut quiet())
            .unwrap()
            .1
            .is_some()
    );
    nodes.push(node(arms[1].body, Scalar::Bool(true), vec![], vec![]));
    nodes[4].children.push(5);
    assert!(
        observation(i.law(), body, Some(4), &nodes, &mut quiet())
            .unwrap()
            .1
            .is_none()
    );
}
