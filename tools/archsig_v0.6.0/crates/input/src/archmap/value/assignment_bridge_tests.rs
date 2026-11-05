use super::*;
use archsig_common::control::{CheckFailure, Signal};
use std::{cell::Cell, rc::Rc};

type Failure = CheckFailure<Box<Issue>>;

// Previous check_assignment entry, with the same Reader and signature.
fn legacy_assignment<E: InputError>(
    value: &Json,
    ty: &Type,
    definitions: &CheckedDefinitions,
    roster: &Roster<'_>,
    namespace: &str,
    control: &Control,
) -> Result<Value, E> {
    let encoded = value.canonical_controlled::<E>(control, Checkpoint::Completion)?;
    let node = archsig_common::json::parse_inner::<E>(
        encoded.as_bytes(),
        control,
        Checkpoint::Completion,
    )?;
    Reader::<E> {
        control: control.clone(),
        error: std::marker::PhantomData,
        definitions,
        roster,
        namespace,
        rebases: &super::super::schema::Rebases::default(),
    }
    .read(&node, ty, "")
}
fn legacy_node(value: &Json) -> JNode {
    archsig_common::json::parse(value.canonical().as_bytes()).unwrap()
}
fn definitions() -> CheckedDefinitions {
    let json = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Bridge","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Bridge.Root","meaning":"root","parameters":[],"fields":[],"alignments":[]},{"kind":"entity","name":"Bridge.Item","meaning":"item","parameters":[{"name":"owner","type":["Ref","Bridge.Root"],"meaning":"owner"}],"fields":[],"alignments":[]},{"kind":"data","name":"Bridge.Choice","meaning":"choice","constructors":[{"name":"Some","arguments":["Z"],"meaning":"some"},{"name":"Empty","arguments":[],"meaning":"empty"}]}]}]}"#;
    crate::definition::check_definitions(&[("bridge", json.as_bytes())]).unwrap()
}
fn roster() -> Roster<'static> {
    Roster {
        types: HashMap::from([
            (("v", "root"), "Bridge.Root"),
            (("v", "item"), "Bridge.Item"),
        ]),
    }
}
fn reference(subject: &str) -> Json {
    Json::Arr(vec![Json::str("v"), Json::str(subject)])
}
fn term(names: &[&str], body: &str) -> Json {
    Json::obj([
        (
            "params",
            Json::Arr(names.iter().map(|name| Json::str(*name)).collect()),
        ),
        ("body", Json::str(body)),
    ])
}
fn data(tag: &str, args: Vec<Json>) -> Json {
    Json::obj([("tag", Json::str(tag)), ("args", Json::Arr(args))])
}

#[test]
fn typed_json_tree_matches_canonical_parse_for_every_variant() {
    let long = "é日本語😀\"\\\n\u{0001}".repeat(300);
    for value in [
        Json::Bool(false),
        Json::Nat(u64::MAX),
        Json::str(&long),
        Json::Arr(vec![
            Json::Bool(true),
            Json::Nat(0),
            Json::str(""),
            Json::Arr(vec![]),
        ]),
        Json::obj([("z", Json::Bool(true)), ("a", Json::str(&long))]),
        Json::obj([(&long, Json::Nat(3))]),
        Json::NodeReferences(vec![]),
        Json::NodeReferences(vec![2, 10, 2, usize::MAX]),
    ] {
        assert_eq!(
            assignment_node::<Box<Issue>>(&value, &Control::unlimited()).unwrap(),
            legacy_node(&value)
        );
    }
    for indices in [vec![], vec![2, 10, 2]] {
        let plain = Json::Arr(
            indices
                .iter()
                .map(|index| Json::obj([("node", Json::str(format!("n{index}")))]))
                .collect(),
        );
        assert_eq!(
            assignment_node::<Box<Issue>>(&Json::NodeReferences(indices), &Control::unlimited())
                .unwrap(),
            legacy_node(&plain)
        );
    }
}

#[test]
fn all_primitive_types_keep_the_previous_values_and_checked_terms() {
    let definitions = definitions();
    let roster = roster();
    for (ty, json) in [
        (Type::Unit, Json::Arr(vec![])),
        (Type::Unit, Json::NodeReferences(vec![])),
        (Type::Bool, Json::Bool(true)),
        (Type::Z, Json::str("-123")),
        (Type::Q, Json::Arr(vec![Json::str("2"), Json::str("3")])),
        (Type::Fp("7".into()), Json::str("6")),
        (Type::Text, Json::str("é\n😀")),
        (Type::Ref("Bridge.Item".into()), reference("item")),
        (
            Type::Owned("Bridge.Item".into(), "owner".into()),
            reference("item"),
        ),
        (
            Type::Tuple(vec![Type::Bool, Type::Z]),
            Json::Arr(vec![Json::Bool(false), Json::str("2")]),
        ),
        (
            Type::List(Box::new(Type::Bool)),
            Json::Arr(vec![Json::Bool(true), Json::Bool(true)]),
        ),
        (
            Type::Set(Box::new(Type::Bool)),
            Json::Arr(vec![Json::Bool(true), Json::Bool(false)]),
        ),
        (
            Type::Option(Box::new(Type::Bool)),
            Json::obj([("none", Json::Bool(true))]),
        ),
        (
            Type::Option(Box::new(Type::Bool)),
            Json::obj([("some", Json::Bool(false))]),
        ),
        (
            Type::Data("Bridge.Choice".into()),
            data("Some", vec![Json::str("3")]),
        ),
        (Type::Data("Bridge.Choice".into()), data("Empty", vec![])),
        (
            Type::Map(
                Box::new(Type::Ref("Bridge.Item".into())),
                Box::new(Type::Ref("Bridge.Root".into())),
            ),
            Json::Arr(vec![Json::Arr(vec![reference("item"), reference("root")])]),
        ),
        (
            Type::Term(vec![Type::Z], Box::new(Type::Z)),
            term(&["x"], "x+1"),
        ),
    ] {
        let old = legacy_assignment::<Box<Issue>>(
            &json,
            &ty,
            &definitions,
            &roster,
            "Bridge",
            &Control::unlimited(),
        )
        .unwrap();
        let new = check_assignment::<Box<Issue>>(
            &json,
            &ty,
            &definitions,
            &roster,
            "Bridge",
            &Control::unlimited(),
        )
        .unwrap();
        assert_eq!(new, old);
        if let (Value::Term(a), Value::Term(b)) = (&new, &old) {
            assert_eq!(a.checked.exprs, b.checked.exprs);
            assert_eq!(a.checked.root, b.checked.root);
            assert_eq!(a.checked.types, b.checked.types);
            assert_eq!(a.checked.references, b.checked.references);
            assert_eq!(a.checked.quantifier_types, b.checked.quantifier_types);
        }
    }
}

#[test]
fn bad_values_keep_issue_code_message_pointer_and_namespace_checks() {
    let definitions = definitions();
    let roster = roster();
    let map = || {
        Type::Map(
            Box::new(Type::Ref("Bridge.Item".into())),
            Box::new(Type::Ref("Bridge.Root".into())),
        )
    };
    for (ty, json) in [
        (Type::Bool, Json::Nat(1)),
        (Type::Unit, Json::Arr(vec![Json::Bool(false)])),
        (Type::Z, Json::str("01")),
        (Type::Q, Json::Arr(vec![Json::str("2"), Json::str("4")])),
        (Type::Q, Json::Arr(vec![Json::str("1"), Json::str("0")])),
        (Type::Fp("7".into()), Json::str("7")),
        (Type::Fp("7".into()), Json::str("-1")),
        (Type::Ref("Bridge.Item".into()), reference("absent")),
        (Type::Ref("Bridge.Item".into()), reference("root")),
        (
            Type::Owned("Bridge.Item".into(), "owner".into()),
            reference("root"),
        ),
        (
            Type::Set(Box::new(Type::Bool)),
            Json::Arr(vec![Json::Bool(true), Json::Bool(true)]),
        ),
        (
            map(),
            Json::Arr(vec![
                Json::Arr(vec![reference("item"), reference("root")]),
                Json::Arr(vec![reference("item"), reference("root")]),
            ]),
        ),
        (map(), Json::Arr(vec![Json::Arr(vec![reference("item")])])),
        (Type::Data("Bridge.Choice".into()), data("Missing", vec![])),
        (Type::Data("Bridge.Choice".into()), data("Some", vec![])),
        (
            Type::Term(vec![Type::Z], Box::new(Type::Z)),
            term(&["x"], "unbound+1"),
        ),
    ] {
        let old = legacy_assignment::<Box<Issue>>(
            &json,
            &ty,
            &definitions,
            &roster,
            "Bridge",
            &Control::unlimited(),
        )
        .unwrap_err();
        let new = check_assignment::<Box<Issue>>(
            &json,
            &ty,
            &definitions,
            &roster,
            "Bridge",
            &Control::unlimited(),
        )
        .unwrap_err();
        assert_eq!(new, old);
    }
    let json = term(
        &[],
        "match Choice.Empty { Empty => true; Some(n) => false; }",
    );
    let ty = Type::Term(vec![], Box::new(Type::Bool));
    for namespace in ["Bridge", "Absent"] {
        let old = legacy_assignment::<Box<Issue>>(
            &json,
            &ty,
            &definitions,
            &roster,
            namespace,
            &Control::unlimited(),
        );
        let new = check_assignment::<Box<Issue>>(
            &json,
            &ty,
            &definitions,
            &roster,
            namespace,
            &Control::unlimited(),
        );
        assert_eq!(old.is_ok(), namespace == "Bridge");
        assert_eq!(new, old);
    }
}

#[test]
fn every_new_tree_and_string_boundary_honors_stop() {
    let text = "é😀".repeat(300);
    let json = Json::obj([(
        &text,
        Json::Arr(vec![Json::str(&text), Json::NodeReferences(vec![2, 10])]),
    )]);
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let c = Control::new(move |_| {
        seen.set(seen.get() + 1);
        None
    });
    assignment_node::<Failure>(&json, &c).unwrap();
    for signal in [Signal::Int, Signal::Term] {
        for at in 1..=count.get() {
            let mut visits = 0;
            let c = Control::new(move |_| {
                visits += 1;
                (visits == at).then_some(signal)
            });
            assert!(
                matches!(assignment_node::<Failure>(&json, &c), Err(CheckFailure::Stopped(s)) if s == signal)
            );
        }
    }
}

#[test]
fn unchanged_reader_rejections_still_yield_to_cancellation() {
    let definitions = definitions();
    let roster = roster();
    let json = Json::Arr(vec![Json::str("2"), Json::str("4")]);
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let c = Control::new(move |point| {
        if point == Checkpoint::ArchMapSchema || point == Checkpoint::ArchMapIteration {
            seen.set(seen.get() + 1);
        }
        None
    });
    assert!(matches!(
        check_assignment::<Failure>(&json, &Type::Q, &definitions, &roster, "Bridge", &c),
        Err(CheckFailure::Input(_))
    ));
    for signal in [Signal::Int, Signal::Term] {
        for at in 1..=count.get() {
            let mut visits = 0;
            let c = Control::new(move |point| {
                if point == Checkpoint::ArchMapSchema || point == Checkpoint::ArchMapIteration {
                    visits += 1;
                }
                (visits == at).then_some(signal)
            });
            assert!(
                matches!(check_assignment::<Failure>(&json, &Type::Q, &definitions, &roster, "Bridge", &c), Err(CheckFailure::Stopped(s)) if s == signal)
            );
        }
    }
}

#[test]
fn deep_trees_and_partial_construction_keep_stack_safe_drop() {
    let mut value = Json::Bool(true);
    for _ in 0..4096 {
        value = Json::Arr(vec![value]);
    }
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let control = Control::new(move |_| {
        seen.set(seen.get() + 1);
        None
    });
    let new = assignment_node::<Failure>(&value, &control).unwrap();
    let old = legacy_node(&value);
    let (mut a, mut b) = (&new, &old);
    for _ in 0..4096 {
        let (JValue::Arr(aa), JValue::Arr(bb)) = (&a.value, &b.value) else {
            panic!()
        };
        assert_eq!((aa.len(), bb.len()), (1, 1));
        a = &aa[0];
        b = &bb[0];
    }
    assert_eq!(a.value, JValue::Bool(true));
    assert_eq!(b.value, JValue::Bool(true));
    for at in [1, 1000, 4097] {
        let mut visits = 0;
        let c = Control::new(move |_| {
            visits += 1;
            (visits == at).then_some(Signal::Term)
        });
        assert!(matches!(
            assignment_node::<Failure>(&value, &c),
            Err(CheckFailure::Stopped(Signal::Term))
        ));
    }
    let value = Json::Arr(vec![value, Json::Bool(false)]);
    let at = count.get() + 2; // outer entry + complete first child + next child entry
    let mut visits = 0;
    let c = Control::new(move |_| {
        visits += 1;
        (visits == at).then_some(Signal::Term)
    });
    assert!(matches!(
        assignment_node::<Failure>(&value, &c),
        Err(CheckFailure::Stopped(Signal::Term))
    ));
}
