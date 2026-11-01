#[path = "common/finite_polynomial_data.rs"]
mod fixture;
use archsig::{
    construction::ConstructionFailure,
    control::{Checkpoint, Control, StopReason},
    input::CheckedInputs,
    observed::finite_polynomial_evaluation::{
        FiniteIntegerFunction as V, FinitePolynomialEvaluation as E, FinitePolynomialFailure as F,
        FinitePolynomialTableKind as K, finite_polynomial_evaluation,
    },
    result::Signal,
    types::Type,
};
use num_bigint::BigInt;
use std::{cell::Cell, collections::BTreeSet, rc::Rc, sync::Arc};
fn quiet() -> Control {
    Control::unlimited()
}
fn run(i: Arc<CheckedInputs>) -> E {
    finite_polynomial_evaluation(i, "Selected", "v", "root", 0, &mut quiet()).unwrap()
}
fn index(e: &E, name: &str) -> usize {
    e.tables()
        .iter()
        .position(|t| {
            e.base().base().base().readings().instances()
                [e.base().occurrences()[t.occurrence].position.instance]
                .declaration()
                .name
                == format!("Selected.{name}")
        })
        .unwrap()
}
fn nums(v: &V) -> Vec<String> {
    v.values().iter().map(ToString::to_string).collect()
}
#[test]
fn all_four_shared_assignments_keep_original_fp_values_and_integer_indicators() {
    let i = fixture::inputs(fixture::BODY);
    let e = run(i.clone());
    assert!(e.is_complete() && e.domain_is_complete());
    assert_eq!(e.symbols().len(), 2);
    assert_eq!(e.domain().len(), 4);
    assert_eq!(e.observed_point(), Some(1));
    assert_eq!(
        e.symbols()
            .iter()
            .map(|s| s.slot.field.as_str())
            .collect::<Vec<_>>(),
        ["Pattern.Part.quantity", "Pattern.Part.other"]
    );
    assert!(
        e.symbols()
            .iter()
            .all(|s| s.ty == Type::Fp("2".into()) && s.ring == 0)
    );
    let points: Vec<_> = e
        .domain()
        .iter()
        .map(|p| {
            p.values()
                .iter()
                .map(|v| v.wire().canonical())
                .collect::<Vec<_>>()
        })
        .collect();
    assert_eq!(
        points,
        vec![
            vec!["\"0\"", "\"0\""],
            vec!["\"0\"", "\"1\""],
            vec!["\"1\"", "\"0\""],
            vec!["\"1\"", "\"1\""]
        ]
    );
    for (name, expected) in [
        ("ax", vec!["0", "0", "1", "1"]),
        ("ay", vec!["1", "0", "1", "0"]),
        ("diff", vec!["0", "1", "1", "0"]),
        ("duplicate", vec!["0", "0", "0", "0"]),
    ] {
        let t = &e.tables()[index(&e, name)];
        assert_eq!(t.kind, K::Evaluated);
        assert_eq!(nums(t.nonzero().unwrap()), expected);
        assert_eq!(
            t.values()
                .unwrap()
                .iter()
                .map(|v| v.wire().canonical())
                .collect::<Vec<_>>(),
            expected
                .iter()
                .map(|v| format!("\"{v}\""))
                .collect::<Vec<_>>()
        );
        let q = &e.base().occurrences()[t.occurrence];
        assert_eq!(q.epsilon.as_ref().unwrap(), &t.values().unwrap()[1]);
        assert_eq!(q.evaluated_nu, q.epsilon);
        assert!(q.nu.is_some());
    }
    assert_eq!(e.base().rings()[0].required_generators.len(), 2);
    assert_eq!(e.base().rings()[0].symbols.len(), 2);
    e.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn integer_function_ring_uses_pointwise_exact_arithmetic_and_rejects_other_domains() {
    let e = run(fixture::inputs(fixture::BODY));
    let f = run(fixture::inputs(fixture::BODY));
    let z = e.zero(&mut quiet()).unwrap();
    let one = e.one(&mut quiet()).unwrap();
    let a = e.basis(0, &mut quiet()).unwrap();
    let b = e.basis(1, &mut quiet()).unwrap();
    assert_eq!(nums(&a), ["1", "0", "0", "0"]);
    assert!(
        e.is_zero(&e.mul(&a, &b, &mut quiet()).unwrap(), &mut quiet())
            .unwrap()
    );
    assert!(
        e.equal(&a, &e.mul(&a, &a, &mut quiet()).unwrap(), &mut quiet())
            .unwrap()
    );
    assert!(!e.equal(&a, &one, &mut quiet()).unwrap());
    let huge = BigInt::from(10u32).pow(60);
    let k = e.constant(huge.clone(), &mut quiet()).unwrap();
    let minus = e.constant(-&huge, &mut quiet()).unwrap();
    assert!(
        e.equal(&e.add(&k, &minus, &mut quiet()).unwrap(), &z, &mut quiet())
            .unwrap()
    );
    let two = e.add(&one, &one, &mut quiet()).unwrap();
    assert_eq!(e.at(&two, 3, &mut quiet()).unwrap(), BigInt::from(2));
    assert!(!e.is_zero(&two, &mut quiet()).unwrap());
    assert!(
        e.equal(
            &e.sub(&two, &one, &mut quiet()).unwrap(),
            &one,
            &mut quiet()
        )
        .unwrap()
    );
    let sum = e.add(&a, &b, &mut quiet()).unwrap();
    let left = e.mul(&k, &sum, &mut quiet()).unwrap();
    let right = e
        .add(
            &e.mul(&k, &a, &mut quiet()).unwrap(),
            &e.mul(&k, &b, &mut quiet()).unwrap(),
            &mut quiet(),
        )
        .unwrap();
    assert!(e.equal(&left, &right, &mut quiet()).unwrap());
    assert!(matches!(
        e.add(&a, &f.one(&mut quiet()).unwrap(), &mut quiet()),
        Err(ConstructionFailure::InvalidSelection(_))
    ));
    assert!(e.at(&a, 4, &mut quiet()).is_err());
    assert!(e.basis(4, &mut quiet()).is_err());
}
#[test]
fn different_prime_fields_share_a_typed_domain_and_nonzero_two_is_integer_one() {
    let body = format!("{}law optional third(c:Part):c.third=0;", fixture::BODY);
    let e = run(fixture::inputs(&body));
    assert_eq!(e.symbols().len(), 3);
    assert_eq!(e.domain().len(), 12);
    let x = e
        .symbols()
        .iter()
        .position(|s| s.slot.field == "Pattern.Part.quantity")
        .unwrap();
    let y = e
        .symbols()
        .iter()
        .position(|s| s.slot.field == "Pattern.Part.other")
        .unwrap();
    let z = e
        .symbols()
        .iter()
        .position(|s| s.slot.field == "Pattern.Part.third")
        .unwrap();
    assert_eq!(e.symbols()[z].ty, Type::Fp("3".into()));
    assert_ne!(e.symbols()[x].ring, e.symbols()[z].ring);
    let mut observed = BTreeSet::new();
    let t = &e.tables()[index(&e, "third")];
    for (j, p) in e.domain().iter().enumerate() {
        let values: Vec<_> = [x, y, z]
            .iter()
            .map(|i| p.values()[*i].wire().canonical())
            .collect();
        observed.insert(values);
        assert_eq!(t.values().unwrap()[j], p.values()[z]);
        let n = p.values()[z].wire().canonical();
        assert_eq!(
            t.nonzero().unwrap().values()[j],
            BigInt::from(if n == "\"0\"" { 0 } else { 1 })
        );
    }
    let expected: BTreeSet<_> = (0..2)
        .flat_map(|x| {
            (0..2).flat_map(move |y| {
                (0..3)
                    .map(move |z| vec![format!("\"{x}\""), format!("\"{y}\""), format!("\"{z}\"")])
            })
        })
        .collect();
    assert_eq!(observed, expected);
    let point = e.observed_point().unwrap();
    assert_eq!(t.values().unwrap()[point].wire().canonical(), "\"2\"");
    assert_eq!(
        e.at(t.nonzero().unwrap(), point, &mut quiet()).unwrap(),
        BigInt::from(1)
    );
}
#[test]
fn empty_symbols_mean_one_empty_assignment_and_do_not_make_the_integer_ring_trivial() {
    for body in [
        "",
        "view three():Fp(3)=1;law optional constant(c:Part):three()=2;",
    ] {
        let e = run(fixture::inputs(body));
        assert!(e.is_complete() && e.domain_is_complete());
        assert!(e.symbols().is_empty());
        assert_eq!(e.domain().len(), 1);
        assert!(e.domain()[0].values().is_empty());
        assert_eq!(e.observed_point(), Some(0));
        assert!(
            !e.equal(
                &e.zero(&mut quiet()).unwrap(),
                &e.one(&mut quiet()).unwrap(),
                &mut quiet()
            )
            .unwrap()
        );
        if !body.is_empty() {
            let t = &e.tables()[index(&e, "constant")];
            assert_eq!(t.values().unwrap()[0].wire().canonical(), "\"2\"");
            assert_eq!(nums(t.nonzero().unwrap()), ["1"]);
        } else {
            assert!(e.tables().is_empty());
        }
    }
}
#[test]
fn finite_parameters_and_tuple_components_keep_their_original_occurrences() {
    let e = run(fixture::inputs(
        "law required family(c:Part,n:Fp(2)):(c.quantity,n+1)=(n,0);",
    ));
    assert_eq!(e.domain().len(), 2);
    assert_eq!(e.tables().len(), 4);
    let mut rows = BTreeSet::new();
    for t in e.tables() {
        let q = &e.base().occurrences()[t.occurrence];
        rows.insert((q.row, q.component.clone()));
        let expected = match (q.row, q.component.as_slice()) {
            (Some(0), [0]) => vec!["0", "1"],
            (Some(0), [1]) => vec!["1", "1"],
            (Some(1), [0]) => vec!["1", "0"],
            (Some(1), [1]) => vec!["0", "0"],
            _ => panic!("{q:?}"),
        };
        assert_eq!(nums(t.nonzero().unwrap()), expected);
    }
    assert_eq!(rows.len(), 4);
}
#[test]
fn missing_observation_is_not_an_observed_completion_and_unavailable_readings_are_not_zero() {
    let missing = fixture::MAP.replace(
        r#"{"id":"x","subject":"p","field":"Pattern.Part.quantity","value":"0","origin":"model"},"#,
        "",
    );
    let i = fixture::with_map(fixture::BODY, &missing);
    let e = run(i.clone());
    assert!(e.domain_is_complete());
    assert_eq!(e.domain().len(), 4);
    assert!(e.observed_point().is_none());
    assert!(
        e.base().rings()[0]
            .symbols
            .iter()
            .any(|s| s.value.is_none())
    );
    assert_eq!(
        nums(e.tables()[index(&e, "ax")].nonzero().unwrap()),
        ["0", "0", "1", "1"]
    );
    e.recheck(i, &mut quiet()).unwrap();
    let e = run(fixture::inputs(
        "law optional predicate(c:Part):c.quantity=0 or c.other=0;view integer():Z=2;law optional infinite(c:Part):integer()=1;",
    ));
    assert!(
        e.tables()
            .iter()
            .all(|t| t.kind == K::OutsideFinitePolynomialReading
                && t.values().is_none()
                && t.nonzero().is_none())
    );
}
#[test]
fn changed_law_provenance_and_invalid_object_are_rejected() {
    let i = fixture::inputs(fixture::BODY);
    let e = run(i);
    assert!(
        e.recheck(
            fixture::inputs(&fixture::BODY.replace("c.other=1", "c.other=0")),
            &mut quiet()
        )
        .is_err()
    );
    assert!(
        e.recheck(
            fixture::with_map(fixture::BODY, &fixture::MAP.replace("\"r1\"", "\"r2\"")),
            &mut quiet()
        )
        .is_err()
    );
    assert!(
        finite_polynomial_evaluation(
            fixture::inputs(fixture::BODY),
            "Selected",
            "v",
            "root",
            99,
            &mut quiet()
        )
        .is_err()
    );
}
#[test]
fn a_finite_but_uncompiled_branch_does_not_become_a_zero_function() {
    let e = run(fixture::inputs(
        "law optional branch(c:Part):(if c.quantity=0 then c.quantity else c.other)=0;",
    ));
    let t = &e.tables()[index(&e, "branch")];
    assert_eq!(t.kind, K::MissingPolynomial);
    assert!(t.values().is_none() && t.nonzero().is_none());
    let q = &e.base().occurrences()[t.occurrence];
    assert!(q.nu.is_none());
    assert_eq!(q.epsilon.as_ref().unwrap().wire().canonical(), "\"0\"");
    assert!(!q.operands.is_empty());
}
fn stopped(at: usize, signal: Signal) -> (Control, Rc<Cell<usize>>) {
    let count = Rc::new(Cell::new(0));
    let found = count.clone();
    let c = Control::new(move |p| {
        if p == Checkpoint::FinitePolynomialTable {
            found.set(found.get() + 1);
        }
        (found.get() >= at).then_some(signal)
    });
    (c, count)
}
#[test]
fn table_stops_keep_complete_domain_and_function_prefix_and_freeze_probes() {
    let i = fixture::inputs(fixture::BODY);
    for at in [1, 4] {
        for signal in [Signal::Int, Signal::Term] {
            let (mut c, count) = stopped(at, signal);
            let error = finite_polynomial_evaluation(i.clone(), "Selected", "v", "root", 0, &mut c)
                .unwrap_err();
            let F::Reading { partial, cause } = error else {
                panic!("{error:?}")
            };
            assert_eq!(
                cause,
                ConstructionFailure::Stopped(StopReason::Cancelled(signal))
            );
            assert!(partial.base().occurrences().iter().any(|q| {
                q.epsilon
                    .as_ref()
                    .is_some_and(|v| v.wire().canonical() == "\"1\"")
            }));
            assert!(partial.domain_is_complete());
            assert_eq!(partial.tables().len(), at);
            assert_eq!(partial.is_complete(), at == 4);
            for t in partial.tables() {
                assert_eq!(t.values().unwrap().len(), 4);
                assert_eq!(t.nonzero().unwrap().values().len(), 4);
            }
            let frozen = count.get();
            assert!(partial.zero(&mut c).is_err());
            assert_eq!(count.get(), frozen);
            assert!(c.checkpoint(Checkpoint::FinitePolynomialTable).is_err());
            assert_eq!(count.get(), frozen);
        }
    }
}
