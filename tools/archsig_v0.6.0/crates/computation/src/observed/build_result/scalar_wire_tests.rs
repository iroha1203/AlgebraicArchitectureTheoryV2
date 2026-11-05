use super::*;
use std::mem::size_of;

fn reference(subject: &str) -> Scalar {
    Scalar::Subject {
        snapshot: "v".into(),
        subject: subject.into(),
        entity: "R.Item".into(),
    }
}

// This is the previous generic Part, not finite_law_diagram::Part.
#[allow(dead_code)]
#[derive(PartialEq, Eq)]
struct LegacyPart {
    ty: NodeType,
    construction: &'static str,
    wire: Json,
    arguments: Vec<NodeRef>,
    support: Vec<Fact>,
    scope: Scope,
    reasons: Vec<Reason>,
    judgment: Option<Judgment>,
    evidence: Vec<NodeRef>,
    scalar: Option<Scalar>,
    domain_type: Option<Type>,
}

#[test]
fn optional_wire_does_not_grow_json_or_generic_part() {
    assert_eq!(size_of::<Option<Json>>(), size_of::<Json>());
    assert!(size_of::<Part>() <= size_of::<LegacyPart>());
}

#[test]
fn scalar_parts_preserve_previous_wire_without_retaining_json() {
    use archsig_common::names::QualifiedName;
    let term = super::super::term::Term {
        params: vec![("x".into(), Type::Bool)],
        returns: Type::Bool,
        body: "x".into(),
        root: 0,
        offset: 0,
        nodes: BTreeMap::new(),
        types: BTreeMap::new(),
        references: vec![],
        quantifier_types: BTreeMap::new(),
    };
    // Serialization shapes only: Term checking and Path resolution have their own fixtures.
    let values = vec![
        Scalar::Unit,
        Scalar::Text("text".into()),
        Scalar::Z((-123).into()),
        Scalar::Q(2.into(), 3.into()),
        Scalar::Fp {
            modulus: "7".into(),
            value: 4.into(),
        },
        Scalar::Bool(true),
        Scalar::Subject {
            snapshot: "v".into(),
            subject: "s".into(),
            entity: "E".into(),
        },
        Scalar::Term(Box::new(term)),
        Scalar::Data {
            family: "F".into(),
            constructor: QualifiedName::parse("F.C".into()),
            args: vec![Scalar::Bool(false)],
        },
        Scalar::Map {
            domain: "R.Item".into(),
            codomain: "R.Item".into(),
            pairs: vec![
                (reference("2"), reference("b")),
                (reference("1"), reference("a")),
            ],
        },
        Scalar::List {
            element: Type::Bool,
            items: vec![Scalar::Bool(true), Scalar::Bool(false)],
        },
        Scalar::Set {
            element: Type::Z,
            items: vec![Scalar::Z(2.into()), Scalar::Z(1.into())],
        },
        Scalar::Option {
            element: Type::Bool,
            value: None,
        },
        Scalar::Option {
            element: Type::Bool,
            value: Some(Box::new(Scalar::Bool(false))),
        },
        Scalar::Tuple(vec![Scalar::Unit, Scalar::Text("nested".into())]),
    ];
    let control = Control::unlimited();
    let graph = Graph::new(&control);
    let mut builder = Builder {
        g: &graph,
        base: 0,
        parts: vec![],
    };
    for scalar in values {
        // The old push expression was scalar.wire() plus Some(scalar.clone()).
        let expected = scalar.wire().canonical();
        let ty = NodeType::Value(scalar.ty());
        let reference = builder
            .scalar(ty.clone(), "binding", scalar, vec![])
            .unwrap();
        let part = &builder.parts[reference.0];
        assert_eq!(part.ty, ty);
        assert!(part.wire_ref().is_none());
        assert!(part.evidence_kind().is_none());
        assert_eq!(part.wire().canonical(), expected);
        assert_eq!(part.clone(), *part);
        let mut changed = part.clone();
        changed.scalar = Some(Scalar::Unit);
        if part.scalar != changed.scalar {
            assert_ne!(changed, *part);
        }
    }
    let wire = Json::obj([
        ("kind", Json::str("counterexample")),
        ("data", Json::Arr(vec![])),
    ]);
    let reference = builder
        .push(
            NodeType::Proposition,
            "proposition",
            wire.clone(),
            vec![],
            None,
        )
        .unwrap();
    let part = &builder.parts[reference.0];
    assert_eq!(part.wire_ref(), Some(&wire));
    assert_eq!(part.wire(), wire);
    assert_eq!(part.evidence_kind(), Some(EvidenceKind::Counterexample));
    let mut changed = part.clone();
    *changed.wire_mut().unwrap() = Json::Bool(false);
    assert_ne!(changed, *part);
}

fn legacy(part: &Part) -> LegacyPart {
    LegacyPart {
        ty: part.ty.clone(),
        construction: part.construction,
        wire: part
            .wire_ref()
            .map_or_else(|| part.scalar.as_ref().unwrap().wire(), Clone::clone),
        arguments: part.arguments.clone(),
        support: part.support.clone(),
        scope: part.scope.clone(),
        reasons: part.reasons.clone(),
        judgment: part.judgment.clone(),
        evidence: part.evidence.clone(),
        scalar: part.scalar.clone(),
        domain_type: part.domain_type.clone(),
    }
}

#[test]
fn source_part_equality_keeps_the_previous_wire_order_guard() {
    let control = Control::unlimited();
    let graph = Graph::new(&control);
    let mut builder = Builder {
        g: &graph,
        base: 0,
        parts: vec![],
    };
    let set = || Scalar::Set {
        element: Type::Z,
        items: vec![Scalar::Z(1.into()), Scalar::Z(2.into())],
    };
    let map = || Scalar::Map {
        domain: "R.Item".into(),
        codomain: "R.Item".into(),
        pairs: vec![
            (reference("1"), reference("false")),
            (reference("2"), reference("true")),
        ],
    };
    for scalar in [
        set(),
        map(),
        Scalar::Tuple(vec![set()]),
        Scalar::Option {
            element: set().ty(),
            value: Some(Box::new(set())),
        },
    ] {
        let r = builder
            .scalar(NodeType::Value(scalar.ty()), "binding", scalar, vec![])
            .unwrap();
        let part = &builder.parts[r.0];
        let mut changed = part.clone();
        fn reverse(value: &mut Scalar) {
            match value {
                Scalar::Set { items, .. } => items.reverse(),
                Scalar::Map { pairs, .. } => pairs.reverse(),
                Scalar::Tuple(items) => reverse(&mut items[0]),
                Scalar::Option {
                    value: Some(value), ..
                } => reverse(value),
                _ => panic!("fixture"),
            }
        }
        reverse(changed.scalar.as_mut().unwrap());
        assert_eq!(part.scalar, changed.scalar);
        assert_ne!(legacy(part).wire, legacy(&changed).wire);
        assert_ne!(*part, changed);
        assert_eq!(*part == changed, legacy(part) == legacy(&changed));
    }
    // Hidden type metadata is checked semantically, while equal JSON shape does
    // not acquire a new ordered-type restriction during wire comparison.
    let a = Scalar::Set {
        element: Type::Bool,
        items: vec![
            Scalar::Fp {
                modulus: "5".into(),
                value: 1.into(),
            },
            Scalar::Fp {
                modulus: "7".into(),
                value: 1.into(),
            },
        ],
    };
    let mut b = a.clone();
    if let Scalar::Set { items, .. } = &mut b {
        items.reverse();
    }
    assert_eq!(a, b);
    assert_eq!(a.wire(), b.wire());
    assert!(same_scalar_wire(&a, &b));
    // Different typed variants may also have the same JSON array shape.
    assert!(same_scalar_wire(&Scalar::Unit, &Scalar::Tuple(vec![])));
}

#[test]
fn wire_order_check_does_not_compare_hidden_scalar_metadata_again() {
    use archsig_common::names::QualifiedName;
    let term = super::super::term::Term {
        params: vec![("x".into(), Type::Bool)],
        returns: Type::Bool,
        body: "x".into(),
        root: 0,
        offset: 0,
        nodes: BTreeMap::new(),
        types: BTreeMap::new(),
        references: vec![],
        quantifier_types: BTreeMap::new(),
    };
    let mut other_term = term.clone();
    other_term.offset = 10;
    let pairs = vec![
        (
            Scalar::Term(Box::new(term)),
            Scalar::Term(Box::new(other_term)),
        ),
        (
            Scalar::Subject {
                snapshot: "v".into(),
                subject: "s".into(),
                entity: "E".into(),
            },
            Scalar::Subject {
                snapshot: "v".into(),
                subject: "s".into(),
                entity: "F".into(),
            },
        ),
        (
            Scalar::Data {
                family: "F".into(),
                constructor: QualifiedName::parse("F.C".into()),
                args: vec![],
            },
            Scalar::Data {
                family: "G".into(),
                constructor: QualifiedName::parse("G.C".into()),
                args: vec![],
            },
        ),
    ];
    let control = Control::unlimited();
    let graph = Graph::new(&control);
    let mut builder = Builder {
        g: &graph,
        base: 0,
        parts: vec![],
    };
    for (a, b) in pairs {
        // Deliberately exercise the old Eq relation on serialization shapes;
        // these mixed hidden-type sets do not assert input type admissibility.
        assert_ne!(a, b);
        assert_eq!(a.wire(), b.wire());
        let scalar = Scalar::Set {
            element: Type::Unit,
            items: vec![a, b],
        };
        let r = builder
            .scalar(NodeType::Value(scalar.ty()), "binding", scalar, vec![])
            .unwrap();
        let part = &builder.parts[r.0];
        let mut changed = part.clone();
        if let Some(Scalar::Set { items, .. }) = &mut changed.scalar {
            items.reverse();
        }
        assert!(legacy(part) == legacy(&changed));
        assert_eq!(*part, changed);
    }
}

#[test]
fn scalar_wire_order_comparison_keeps_deep_container_stack_growth() {
    fn nested(leaf: bool) -> Scalar {
        let mut value = Scalar::Bool(leaf);
        for depth in 0..2048 {
            value = match depth % 4 {
                0 => Scalar::Tuple(vec![value]),
                1 => Scalar::Option {
                    element: Type::Unit,
                    value: Some(Box::new(value)),
                },
                2 => Scalar::Map {
                    domain: "R.Item".into(),
                    codomain: "R.Item".into(),
                    pairs: vec![(Scalar::Unit, value)],
                },
                _ => Scalar::Data {
                    family: "F".into(),
                    constructor: archsig_common::names::QualifiedName::parse("F.C".into()),
                    args: vec![value],
                },
            };
        }
        value
    }
    // Serialization depth fixture, not an input type admissibility assertion.
    let a = nested(true);
    let b = nested(true);
    let c = nested(false);
    assert!(same_scalar_wire(&a, &b));
    assert!(!same_scalar_wire(&a, &c));
    assert_eq!(a.wire(), b.wire());
    assert_ne!(a.wire(), c.wire());
}

#[test]
fn path_parts_keep_the_original_typed_reference_wire_and_equality() {
    let control = Control::unlimited();
    let graph = Graph::new(&control);
    let mut builder = Builder {
        g: &graph,
        base: 0,
        parts: vec![],
    };
    let source = builder
        .scalar(
            NodeType::Value(Type::Ref("E".into())),
            "binding",
            Scalar::Subject {
                snapshot: "v".into(),
                subject: "s".into(),
                entity: "E".into(),
            },
            vec![],
        )
        .unwrap();
    let path = super::super::path_value::PathValue {
        reading: "R".into(),
        snapshot: "v".into(),
        subject: "s".into(),
        entity: "E".into(),
        step: None,
    };
    let wire = Json::obj([
        ("reading", Json::str("R")),
        ("source", source.wire()),
        ("target", source.wire()),
        ("generators", Json::Arr(vec![])),
    ]);
    let reference = builder.path(path, wire.clone(), vec![source]).unwrap();
    let part = &builder.parts[reference.0];
    assert!(matches!(&part.scalar, Some(Scalar::Path(_))));
    assert_eq!(part.wire_ref(), Some(&wire));
    assert_eq!(part.wire(), wire);
    assert!(part.evidence_kind().is_none());
    assert!(*part == part.clone());
    for change_path in [false, true] {
        let mut changed = part.clone();
        if change_path {
            let Some(Scalar::Path(path)) = &mut changed.scalar else {
                unreachable!()
            };
            path.reading = "other".into();
        } else {
            *changed.wire_mut().unwrap() = Json::Bool(false);
        }
        assert!(legacy(part) != legacy(&changed));
        assert_ne!(*part, changed);
    }
}
