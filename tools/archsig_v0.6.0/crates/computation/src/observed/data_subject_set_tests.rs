use super::*;
use archsig_common::control::{Signal, quiet};
use std::{cell::Cell, rc::Rc};

fn subject(snapshot: &str, id: &str, entity: &str) -> Scalar {
    Scalar::Subject {
        snapshot: snapshot.into(),
        subject: id.into(),
        entity: entity.into(),
    }
}
fn linear_set(element: Type, items: &[Scalar]) -> Result<Scalar, ValidationFailure> {
    let c = quiet();
    let mut retained = Vec::new();
    for item in items {
        if item.ty() != element {
            return Err(internal!("test incompatible element").into());
        }
        if !contains(&retained, item, &c)? {
            retained.push(item.clone());
        }
    }
    Ok(Scalar::Set {
        element,
        items: retained,
    })
}
#[test]
fn subject_set_keeps_exact_identity_first_order_and_type_rejection() {
    let ty = Type::Ref("Example.Node".into());
    let a = subject("v", "n", "Example.Node");
    let b = subject("w", "n", "Example.Node");
    let c = subject("v", "m", "Example.Node");
    for items in [
        vec![],
        vec![a.clone(), b.clone(), a.clone(), c.clone(), b.clone()],
        vec![b.clone(), c.clone(), a.clone(), c.clone()],
    ] {
        let actual = set(ty.clone(), &items, &quiet()).unwrap();
        let expected = linear_set(ty.clone(), &items).unwrap();
        let (
            Scalar::Set { items: actual, .. },
            Scalar::Set {
                items: expected, ..
            },
        ) = (&actual, &expected)
        else {
            panic!("set");
        };
        assert_eq!(
            actual, expected,
            "exact first-occurrence sequence, not only unordered Set equality"
        );
        assert!(check_shape(&set(ty.clone(), &items, &quiet()).unwrap(), &quiet()).is_ok());
    }
    assert!(!equal(&a, &b, &quiet()).unwrap());
    assert!(!equal(&a, &c, &quiet()).unwrap());
    let wrong = subject("v", "n", "Example.Other");
    assert!(set(ty.clone(), &[a.clone(), wrong.clone()], &quiet()).is_err());
    assert!(
        equal(&a, &wrong, &quiet()).is_err(),
        "different entity type remains a typed error"
    );
    assert!(!candidate_equal(&a, &wrong, &quiet()).unwrap());
    let malformed = Scalar::Set {
        element: ty.clone(),
        items: vec![a.clone(), a.clone()],
    };
    assert!(check_shape(&malformed, &quiet()).is_err());
    let wrong_type = Scalar::Set {
        element: ty,
        items: vec![a, wrong],
    };
    assert!(check_shape(&wrong_type, &quiet()).is_err());
}
#[test]
fn non_subject_set_members_keep_nested_set_semantic_equality() {
    let a = Scalar::Set {
        element: Type::Bool,
        items: vec![Scalar::Bool(true), Scalar::Bool(false)],
    };
    let b = Scalar::Set {
        element: Type::Bool,
        items: vec![Scalar::Bool(false), Scalar::Bool(true)],
    };
    assert!(equal(&a, &b, &quiet()).unwrap());
    let ty = Type::Set(Box::new(Type::Bool));
    let items = vec![a.clone(), b.clone()];
    let actual = set(ty.clone(), &items, &quiet()).unwrap();
    assert_eq!(actual, linear_set(ty.clone(), &items).unwrap());
    let Scalar::Set {
        items: retained, ..
    } = &actual
    else {
        panic!("set")
    };
    assert_eq!(retained.len(), 1);
    assert_eq!(retained[0], a);
    assert!(check_shape(&actual, &quiet()).is_ok());
    assert!(
        check_shape(&Scalar::Set { element: ty, items }, &quiet()).is_err(),
        "fallback still rejects semantic duplicates"
    );
}
#[test]
fn subject_roster_construction_and_raw_shape_do_not_walk_all_prior_members() {
    const N: usize = 256;
    let items = (0..N)
        .map(|i| subject("v", &format!("n{i}"), "Example.Node"))
        .collect::<Vec<_>>();
    for shape in [false, true] {
        let probes = Rc::new(Cell::new(0));
        let observed = probes.clone();
        let c = Control::new(move |_| {
            let next = observed.get() + 1;
            observed.set(next);
            (next > 20 * N).then_some(Signal::Int)
        });
        if shape {
            check_shape(
                &Scalar::Set {
                    element: Type::Ref("Example.Node".into()),
                    items: items.clone(),
                },
                &c,
            )
            .unwrap();
        } else {
            let actual = set(Type::Ref("Example.Node".into()), &items, &c).unwrap();
            let Scalar::Set { items: actual, .. } = &actual else {
                panic!("set")
            };
            assert_eq!(actual.as_slice(), items.as_slice());
        }
        assert!(
            probes.get() <= 20 * N,
            "a quadratic prefix comparison fails this linear checkpoint bound"
        );
        assert_eq!(c.stop_reason(), None);
    }
}
#[test]
fn subject_set_index_obeys_int_term_and_leaves_original_values_unchanged() {
    let items = (0..32)
        .map(|i| subject("v", &format!("n{i}"), "Example.Node"))
        .collect::<Vec<_>>();
    let original = items.clone();
    for signal in [Signal::Int, Signal::Term] {
        for shape in [false, true] {
            let count = Rc::new(Cell::new(0));
            let observed = count.clone();
            let c = Control::new(move |_| {
                let next = observed.get() + 1;
                observed.set(next);
                (next == 20).then_some(signal)
            });
            let outcome = if shape {
                check_shape(
                    &Scalar::Set {
                        element: Type::Ref("Example.Node".into()),
                        items: items.clone(),
                    },
                    &c,
                )
            } else {
                set(Type::Ref("Example.Node".into()), &items, &c).map(|_| ())
            };
            assert!(matches!(outcome,Err(ValidationFailure::Stop(actual))if actual==signal));
            assert_eq!(c.stop_reason(), Some(signal));
            assert_eq!(items, original);
            // A stopped operation keeps no index for the next independent call.
            let fresh = set(Type::Ref("Example.Node".into()), &items, &quiet()).unwrap();
            assert!(check_shape(&fresh, &quiet()).is_ok());
        }
    }
}
