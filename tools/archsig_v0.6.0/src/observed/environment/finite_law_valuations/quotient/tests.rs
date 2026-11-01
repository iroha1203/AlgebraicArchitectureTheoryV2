use super::*;
#[allow(dead_code)]
mod fixture {
    include!("../../../../../tests/common/primitive_valuation_data.rs");
}
use crate::control::quiet;
fn subject(name: &str) -> Scalar {
    Scalar::Subject {
        snapshot: "v".into(),
        subject: name.into(),
        entity: if name == "root" || name == "r2" {
            "Pattern.Root"
        } else {
            "Pattern.Part"
        }
        .into(),
    }
}
fn selected(names: &[&str]) -> Vec<(String, Vec<(String, Scalar)>)> {
    names
        .iter()
        .map(|name| (format!("Selected.{name}"), vec![("c".into(), subject("p"))]))
        .collect()
}
fn guarded() -> (Arc<CheckedInputs>, FiniteLawFamilyValuations) {
    let i = fixture::with_body(
        fixture::MAP,
        "law required pair(c:Part) when c.flag:c.pair=(0,true);law optional extra(c:Part):false;",
    );
    let r = finite_law_family_valuations(&i, &selected(&["pair", "extra"]), &quiet()).unwrap();
    (i, r)
}
fn strings(f: &FiniteIntegerFunction) -> Vec<String> {
    f.values().iter().map(ToString::to_string).collect()
}
#[test]
fn integer_functions_share_one_origin_and_keep_arbitrary_precision_arithmetic() {
    let i = fixture::with_body(fixture::MAP, "law required zero(c:Part):c.quantity=0;");
    let r = finite_law_family_valuations(&i, &selected(&["zero"]), &quiet()).unwrap();
    let ring = r.integer_ring(&quiet()).unwrap();
    assert_eq!(ring.dimension(), 2);
    let big =
        BigInt::parse_bytes(b"100000000000000000000000000000000000000000000000003", 10).unwrap();
    let a = ring.constant(big.clone(), &quiet()).unwrap();
    let b = ring.constant((-7).into(), &quiet()).unwrap();
    let sum = ring.add(&a, &b, &quiet()).unwrap();
    let expected =
        BigInt::parse_bytes(b"99999999999999999999999999999999999999999999999996", 10).unwrap();
    assert_eq!(sum.values(), &[expected.clone(), expected]);
    let difference = ring.sub(&a, &b, &quiet()).unwrap();
    assert_eq!(difference.values(), &[&big + 7, &big + 7]);
    let product = ring.mul(&a, &b, &quiet()).unwrap();
    assert_eq!(product.values(), &[&big * -7, &big * -7]);
    let zero = ring.zero(&quiet()).unwrap();
    let one = ring.one(&quiet()).unwrap();
    assert_eq!(strings(&zero), vec!["0", "0"]);
    assert_eq!(strings(&one), vec!["1", "1"]);
    assert!(ring.is_zero(&zero, &quiet()).unwrap());
    assert!(!ring.is_zero(&one, &quiet()).unwrap());
    assert!(
        ring.equal(&ring.sub(&sum, &b, &quiet()).unwrap(), &a, &quiet())
            .unwrap()
    );
    assert!(!ring.equal(&a, &b, &quiet()).unwrap());
    assert_eq!(ring.at(&a, 1, &quiet()).unwrap(), big);
    let e0 = ring.basis(0, &quiet()).unwrap();
    let e1 = ring.basis(1, &quiet()).unwrap();
    assert_eq!(strings(&e0), vec!["1", "0"]);
    assert_eq!(strings(&e1), vec!["0", "1"]);
    assert!(
        ring.equal(&ring.add(&e0, &e1, &quiet()).unwrap(), &one, &quiet())
            .unwrap()
    );
    assert!(
        ring.is_zero(&ring.mul(&e0, &e1, &quiet()).unwrap(), &quiet())
            .unwrap()
    );
    assert!(ring.basis(2, &quiet()).is_err());
    assert!(ring.at(&a, 2, &quiet()).is_err());
    assert!(ring.computed(vec![1.into()], &quiet()).is_err());
    let other = finite_law_family_valuations(&i, &selected(&["zero"]), &quiet()).unwrap();
    let foreign = other.integer_ring(&quiet()).unwrap().one(&quiet()).unwrap();
    assert!(ring.add(&one, &foreign, &quiet()).is_err());
    assert!(ring.equal(&one, &foreign, &quiet()).is_err());
}
#[test]
fn original_components_are_generators_in_the_shared_integer_ring() {
    let (i, r) = guarded();
    let ring = r.integer_ring(&quiet()).unwrap();
    let generators = r.required_generators(&quiet()).unwrap();
    assert_eq!(generators.len(), 2);
    assert_eq!(
        generators
            .iter()
            .map(|g| (g.column(), g.component().unwrap().to_vec()))
            .collect::<Vec<_>>(),
        vec![(0, vec![0]), (0, vec![1])]
    );
    assert_eq!(
        strings(generators[0].value()),
        vec!["0", "0", "0", "0", "0", "0", "1", "1"]
    );
    assert_eq!(
        strings(generators[1].value()),
        vec!["0", "0", "0", "0", "1", "0", "1", "0"]
    );
    let whole = r.integer_function(0, None, &quiet()).unwrap();
    let optional = r.integer_function(1, None, &quiet()).unwrap();
    assert_eq!(
        strings(&whole),
        vec!["0", "0", "0", "0", "1", "0", "1", "1"]
    );
    assert_eq!(strings(&optional), vec!["1"; 8]);
    for g in &generators {
        ring.member(g.value(), &quiet()).unwrap();
    }
    assert!(r.integer_function(3, None, &quiet()).is_err());
    assert!(r.integer_function(0, Some(&[2]), &quiet()).is_err());
    assert!(r.integer_function(1, Some(&[]), &quiet()).is_err());
    r.recheck(&i, &quiet()).unwrap();
}
#[test]
fn required_quotient_is_the_actual_projection_and_preserves_ring_operations() {
    let (i, r) = guarded();
    let q = r.required_quotient(&quiet()).unwrap();
    assert_eq!(q.points(), &[0, 1, 2, 3, 5]);
    let source = r.integer_ring(&quiet()).unwrap();
    let target = q.integer_ring(&quiet()).unwrap();
    assert_eq!(target.dimension(), 5);
    let a = source
        .computed((0..8).map(BigInt::from).collect(), &quiet())
        .unwrap();
    let b = source.constant((-3).into(), &quiet()).unwrap();
    let pa = q.project(&a, &quiet()).unwrap();
    let pb = q.project(&b, &quiet()).unwrap();
    assert_eq!(strings(&pa), vec!["0", "1", "2", "3", "5"]);
    let z = q
        .project(&source.zero(&quiet()).unwrap(), &quiet())
        .unwrap();
    let one = q.project(&source.one(&quiet()).unwrap(), &quiet()).unwrap();
    assert!(
        target
            .equal(&z, &target.zero(&quiet()).unwrap(), &quiet())
            .unwrap()
    );
    assert!(
        target
            .equal(&one, &target.one(&quiet()).unwrap(), &quiet())
            .unwrap()
    );
    for op in 0..3 {
        let before = match op {
            0 => source.add(&a, &b, &quiet()),
            1 => source.sub(&a, &b, &quiet()),
            _ => source.mul(&a, &b, &quiet()),
        }
        .unwrap();
        let projected = q.project(&before, &quiet()).unwrap();
        let after = match op {
            0 => target.add(&pa, &pb, &quiet()),
            1 => target.sub(&pa, &pb, &quiet()),
            _ => target.mul(&pa, &pb, &quiet()),
        }
        .unwrap();
        assert!(target.equal(&projected, &after, &quiet()).unwrap());
    }
    for g in r.required_generators(&quiet()).unwrap() {
        assert!(
            target
                .is_zero(&q.project(g.value(), &quiet()).unwrap(), &quiet())
                .unwrap()
        );
    }
    let outside = q
        .project(&source.basis(4, &quiet()).unwrap(), &quiet())
        .unwrap();
    assert!(target.is_zero(&outside, &quiet()).unwrap());
    let kept = q
        .project(&source.basis(5, &quiet()).unwrap(), &quiet())
        .unwrap();
    assert_eq!(strings(&kept), vec!["0", "0", "0", "0", "1"]);
    q.recheck(&i, &quiet()).unwrap();
    assert!(source.member(&kept, &quiet()).is_err());
    assert!(target.member(&a, &quiet()).is_err());
}
#[test]
fn ideal_membership_constructs_and_checks_coefficient_functions() {
    let (i, r) = guarded();
    let q = r.required_quotient(&quiet()).unwrap();
    let ring = r.integer_ring(&quiet()).unwrap();
    let b4 = ring.basis(4, &quiet()).unwrap();
    let b6 = ring.basis(6, &quiet()).unwrap();
    let a = ring
        .mul(&b4, &ring.constant(7.into(), &quiet()).unwrap(), &quiet())
        .unwrap();
    let b = ring
        .mul(
            &b6,
            &ring.constant((-3).into(), &quiet()).unwrap(),
            &quiet(),
        )
        .unwrap();
    let f = ring.add(&a, &b, &quiet()).unwrap();
    let membership = q.ideal_membership(&f, &quiet()).unwrap();
    let FiniteIdealMembership::Member(w) = &membership else {
        panic!()
    };
    assert_eq!(w.generators().len(), 2);
    assert_eq!(w.coefficients().len(), 2);
    assert_eq!(
        strings(&w.coefficients()[0]),
        vec!["0", "0", "0", "0", "0", "0", "-3", "0"]
    );
    assert_eq!(
        strings(&w.coefficients()[1]),
        vec!["0", "0", "0", "0", "7", "0", "0", "0"]
    );
    let mut sum = ring.zero(&quiet()).unwrap();
    for (g, c) in w.generators().iter().zip(w.coefficients()) {
        sum = ring
            .add(&sum, &ring.mul(g.value(), c, &quiet()).unwrap(), &quiet())
            .unwrap();
    }
    assert!(ring.equal(&sum, &f, &quiet()).unwrap());
    q.recheck_membership(&i, &f, &membership, &quiet()).unwrap();
    let f = ring.basis(5, &quiet()).unwrap();
    let membership = q.ideal_membership(&f, &quiet()).unwrap();
    let FiniteIdealMembership::NonMember { projection } = &membership else {
        panic!()
    };
    assert_eq!(strings(projection), vec!["0", "0", "0", "0", "1"]);
    q.recheck_membership(&i, &f, &membership, &quiet()).unwrap();
}
#[test]
fn contradictory_required_laws_give_empty_quotient_and_unit_ideal() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required zero(c:Part):c.quantity=0;law required one(c:Part):c.quantity=1;",
    );
    let r = finite_law_family_valuations(&i, &selected(&["zero", "one"]), &quiet()).unwrap();
    assert_eq!(r.domain.len(), 2);
    let q = r.required_quotient(&quiet()).unwrap();
    assert!(q.points().is_empty());
    let ring = r.integer_ring(&quiet()).unwrap();
    let target = q.integer_ring(&quiet()).unwrap();
    assert!(
        target
            .is_zero(&target.one(&quiet()).unwrap(), &quiet())
            .unwrap()
    );
    let f = ring.constant(5.into(), &quiet()).unwrap();
    let m = q.ideal_membership(&f, &quiet()).unwrap();
    let FiniteIdealMembership::Member(w) = &m else {
        panic!()
    };
    assert_eq!(strings(&w.coefficients()[0]), vec!["0", "5"]);
    assert_eq!(strings(&w.coefficients()[1]), vec!["5", "0"]);
    assert!(
        w.generators()
            .iter()
            .all(|g| g.component() == Some([].as_slice()))
    );
    q.recheck_membership(&i, &f, &m, &quiet()).unwrap();
}
#[test]
fn empty_law_family_has_one_point_and_zero_ideal() {
    let i = fixture::inputs();
    let r = finite_law_family_valuations(&i, &[], &quiet()).unwrap();
    assert_eq!(r.domain(), &[Vec::<Scalar>::new()]);
    assert!(r.required_generators(&quiet()).unwrap().is_empty());
    let q = r.required_quotient(&quiet()).unwrap();
    assert_eq!(q.points(), &[0]);
    let ring = r.integer_ring(&quiet()).unwrap();
    let zero = ring.zero(&quiet()).unwrap();
    let one = ring.one(&quiet()).unwrap();
    let m = q.ideal_membership(&zero, &quiet()).unwrap();
    let FiniteIdealMembership::Member(w) = &m else {
        panic!()
    };
    assert!(w.coefficients().is_empty());
    q.recheck_membership(&i, &zero, &m, &quiet()).unwrap();
    let m = q.ideal_membership(&one, &quiet()).unwrap();
    let FiniteIdealMembership::NonMember { projection } = &m else {
        panic!()
    };
    assert_eq!(strings(projection), vec!["1"]);
    q.recheck_membership(&i, &one, &m, &quiet()).unwrap();
}
#[test]
fn empty_d_keeps_all_original_tuple_generators_and_the_zero_ring() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required typed(r:Root,c:Part[r]):(true,false)=(true,false);",
    );
    let bind = |root: &str| vec![("r".into(), subject(root)), ("c".into(), subject("p"))];
    let r = finite_law_family_valuations(
        &i,
        &[
            ("Selected.typed".into(), bind("root")),
            ("Selected.typed".into(), bind("r2")),
        ],
        &quiet(),
    )
    .unwrap();
    assert!(r.domain.is_empty());
    let generators = r.required_generators(&quiet()).unwrap();
    assert_eq!(generators.len(), 4);
    assert_eq!(
        generators
            .iter()
            .map(|g| (g.column(), g.component().unwrap().to_vec()))
            .collect::<Vec<_>>(),
        vec![(0, vec![0]), (0, vec![1]), (1, vec![0]), (1, vec![1])]
    );
    assert!(generators.iter().all(|g| g.value().values().is_empty()));
    assert!(r.integer_function(0, Some(&[5]), &quiet()).is_err());
    let q = r.required_quotient(&quiet()).unwrap();
    let f = r
        .integer_ring(&quiet())
        .unwrap()
        .constant(99.into(), &quiet())
        .unwrap();
    let m = q.ideal_membership(&f, &quiet()).unwrap();
    let FiniteIdealMembership::Member(w) = &m else {
        panic!()
    };
    assert_eq!(w.coefficients().len(), 4);
    assert!(w.coefficients().iter().all(|f| f.values().is_empty()));
    q.recheck_membership(&i, &f, &m, &quiet()).unwrap();
}
#[test]
fn non_equality_conditions_generate_the_whole_indicator_and_optional_does_not_prune() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required condition(c:Part):c.flag and true;law optional number(c:Part):c.quantity=0;",
    );
    let r =
        finite_law_family_valuations(&i, &selected(&["condition", "number"]), &quiet()).unwrap();
    let gs = r.required_generators(&quiet()).unwrap();
    assert_eq!(gs.len(), 1);
    assert_eq!(gs[0].component(), None);
    assert_eq!(strings(gs[0].value()), vec!["1", "1", "0", "0"]);
    let q = r.required_quotient(&quiet()).unwrap();
    assert_eq!(q.points(), &[2, 3]);
    q.recheck(&i, &quiet()).unwrap();
}
#[test]
fn incomplete_domains_and_unavailable_components_do_not_become_zero_functions() {
    let i = fixture::with_body(fixture::MAP, "law required infinite(c:Part):c.integer=0;");
    let r = finite_law_family_valuations(&i, &selected(&["infinite"]), &quiet()).unwrap();
    assert!(r.integer_ring(&quiet()).is_err());
    assert!(r.integer_function(0, None, &quiet()).is_err());
    assert!(r.required_generators(&quiet()).is_err());
    assert!(r.required_quotient(&quiet()).is_err());
    let i = fixture::with_body(
        fixture::MAP,
        "view left():Term<(Z)->Z> =fn(n:Z)=>n*n;view right():Term<(Z)->Z> =fn(n:Z)=>n*n+0;law required pair(a:Term<(Z)->Z>,b:Term<(Z)->Z>):(0,a)=(1,b);",
    );
    let term = |name: &str| {
        let Signature::View { body, .. } = &i.law().declarations()[name].signature else {
            panic!()
        };
        Scalar::Term(Box::new(
            crate::observed::term::Term::from_law(
                i.law(),
                i.sources().law().bytes(),
                *body,
                &quiet(),
            )
            .unwrap(),
        ))
    };
    let r = finite_law_family_valuations(
        &i,
        &[(
            "Selected.pair".into(),
            vec![
                ("a".into(), term("Selected.left")),
                ("b".into(), term("Selected.right")),
            ],
        )],
        &quiet(),
    )
    .unwrap();
    assert!(r.integer_ring(&quiet()).is_ok());
    assert_eq!(
        strings(&r.integer_function(0, None, &quiet()).unwrap()),
        vec!["1"]
    );
    assert_eq!(
        strings(&r.integer_function(0, Some(&[0]), &quiet()).unwrap()),
        vec!["1"]
    );
    assert!(r.integer_function(0, Some(&[1]), &quiet()).is_err());
    assert!(r.required_generators(&quiet()).is_err());
    assert!(r.required_quotient(&quiet()).is_err());
    r.recheck(&i, &quiet()).unwrap();
}
#[test]
fn quotient_and_membership_recheck_reject_forged_points_origins_generators_and_coefficients() {
    let (i, r) = guarded();
    let q = r.required_quotient(&quiet()).unwrap();
    let ring = r.integer_ring(&quiet()).unwrap();
    let f = ring.basis(4, &quiet()).unwrap();
    let original = q.ideal_membership(&f, &quiet()).unwrap();
    for change in 0..8 {
        let mut m = original.clone();
        let FiniteIdealMembership::Member(w) = &mut m else {
            panic!()
        };
        match change {
            0 => w.coefficients[1] = ring.zero(&quiet()).unwrap(),
            1 => {
                w.coefficients.pop();
            }
            2 => w.generators[0].component = Some(vec![1]),
            3 => w.generators[0].column = 1,
            4 => w.generators[0].value = ring.one(&quiet()).unwrap(),
            5 => w.target = ring.zero(&quiet()).unwrap(),
            6 => w.coefficients[0].owner = Arc::new(()),
            _ => {
                w.generators.pop();
            }
        }
        assert!(
            q.recheck_membership(&i, &f, &m, &quiet()).is_err(),
            "change={change}"
        );
    }
    let mut bad = r.required_quotient(&quiet()).unwrap();
    bad.points[0] = 7;
    assert!(bad.recheck(&i, &quiet()).is_err());
    assert!(bad.project(&f, &quiet()).is_err());
    let f = ring.basis(5, &quiet()).unwrap();
    let m = q.ideal_membership(&f, &quiet()).unwrap();
    let mut wrong = m.clone();
    let FiniteIdealMembership::NonMember { projection } = &mut wrong else {
        panic!()
    };
    *projection = q.integer_ring(&quiet()).unwrap().zero(&quiet()).unwrap();
    assert!(q.recheck_membership(&i, &f, &wrong, &quiet()).is_err());
    let mut wrong = m.clone();
    let FiniteIdealMembership::NonMember { projection } = &mut wrong else {
        panic!()
    };
    projection.owner = Arc::new(());
    assert!(q.recheck_membership(&i, &f, &wrong, &quiet()).is_err());
    let other = fixture::with_body(
        fixture::MAP,
        "law required pair(c:Part) when c.flag:c.pair=(1,true);law optional extra(c:Part):false;",
    );
    assert!(q.recheck(&other, &quiet()).is_err());
}
#[test]
fn equation_schema_is_rechecked_even_when_there_are_no_candidate_rows() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required typed(r:Root,c:Part[r]):(true,false)=(true,false);",
    );
    let bind = |root: &str| vec![("r".into(), subject(root)), ("c".into(), subject("p"))];
    let mut r = finite_law_family_valuations(
        &i,
        &[
            ("Selected.typed".into(), bind("root")),
            ("Selected.typed".into(), bind("r2")),
        ],
        &quiet(),
    )
    .unwrap();
    assert!(r.domain.is_empty());
    r.columns[0].equation_type = Some(Type::Bool);
    assert!(r.recheck(&i, &quiet()).is_err());
    let q = r.required_quotient(&quiet()).unwrap();
    assert!(q.recheck(&i, &quiet()).is_err());
}
#[test]
fn function_and_quotient_fixed_stops_keep_the_completed_base_and_freeze_probe() {
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    let (i, r) = guarded();
    let q = r.required_quotient(&quiet()).unwrap();
    let f = r
        .integer_ring(&quiet())
        .unwrap()
        .basis(4, &quiet())
        .unwrap();
    for point in [Checkpoint::FiniteLawFunction, Checkpoint::FiniteLawQuotient] {
        let run = |at: usize, signal: Signal| {
            let count = Rc::new(Cell::new(0));
            let seen = count.clone();
            let calls = Rc::new(Cell::new(0));
            let sample = calls.clone();
            (
                Control::new(move |p| {
                    sample.set(sample.get() + 1);
                    if p == point {
                        seen.set(seen.get() + 1);
                    }
                    (seen.get() >= at).then_some(signal)
                }),
                count,
                calls,
            )
        };
        let operation = |c: &Control| -> Result<(), ValidationFailure> {
            let ring = r.integer_ring(c)?;
            let one = ring.one(c).map_err(invalid)?;
            let product = ring.mul(&f, &one, c).map_err(invalid)?;
            r.required_generators(c)?;
            let m = q.ideal_membership(&product, c)?;
            q.recheck_membership(&i, &product, &m, c)
        };
        let (mut c, total, _) = run(usize::MAX, Signal::Int);
        operation(&mut c).unwrap();
        let total = total.get();
        assert!(total > 3);
        for at in [1, total / 2, total] {
            for signal in [Signal::Int, Signal::Term] {
                let (mut c, _, calls) = run(at, signal);
                let cause = operation(&mut c).unwrap_err();
                assert!(matches!(cause,ValidationFailure::Stop(ref s) if s==&signal));
                let before = calls.get();
                assert_eq!(c.checkpoint(point), Err(signal));
                assert_eq!(calls.get(), before);
                r.recheck(&i, &quiet()).unwrap();
                assert_eq!(r.required_zero(), Some([0, 1, 2, 3, 5].as_slice()));
            }
        }
    }
}
