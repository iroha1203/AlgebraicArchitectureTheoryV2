use super::*;
#[allow(dead_code)]
mod fixture {
    include!("../../../../tests/common/primitive_valuation_data.rs");
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
fn selected() -> Vec<(String, Vec<(String, Scalar)>)> {
    vec![("Selected.eq".into(), vec![("c".into(), subject("p"))])]
}
fn fact(field: &str) -> Fact {
    Fact {
        snapshot: "v".into(),
        subject: "p".into(),
        field: Some(format!("Pattern.Part.{field}").into()),
        atom: None,
    }
}
fn table(body: &str) -> (Arc<CheckedInputs>, FiniteLawFamilyValuations) {
    let i = fixture::with_body(fixture::MAP, body);
    let r = finite_law_family_valuations(&i, &selected(), &quiet()).unwrap();
    (i, r)
}
fn indicators(r: &FiniteLawFamilyValuations, path: &[usize]) -> Vec<BigInt> {
    r.integer_function(0, Some(path), &quiet())
        .unwrap()
        .values()
        .to_vec()
}
#[test]
fn nested_let_guarded_tuple_has_original_operands_and_shared_component_functions() {
    let (i, r) = table(
        "law required eq(c:Part) when c.flag:let pair=c.pair in let n=pair.0 in (n,pair.1)=(0,true);",
    );
    assert!(r.is_complete());
    assert_eq!(r.positions(), &[fact("flag"), fact("pair")]);
    assert_eq!(r.domain().len(), 8);
    assert_eq!(
        indicators(&r, &[0]),
        [0, 0, 0, 0, 0, 0, 1, 1].map(BigInt::from)
    );
    assert_eq!(
        indicators(&r, &[1]),
        [0, 0, 0, 0, 1, 0, 1, 0].map(BigInt::from)
    );
    assert_eq!(r.required_zero(), Some([0, 1, 2, 3, 5].as_slice()));
    for (point, row) in r.columns()[0].rows().iter().enumerate() {
        let (ty, left, right) = row.operands.as_ref().unwrap();
        assert_eq!(ty, &Type::Tuple(vec![Type::Fp("2".into()), Type::Bool]));
        assert_eq!(left.as_ref(), Some(&r.domain()[point][1]));
        assert_eq!(
            right,
            &Some(Scalar::Tuple(vec![
                Scalar::Fp {
                    modulus: "2".into(),
                    value: 0.into()
                },
                Scalar::Bool(true)
            ]))
        );
        assert!(row.support.contains(&fact("flag")));
        assert!(row.support.contains(&fact("pair")));
        assert!(row.scope.assignments);
    }
    r.recheck(&i, &quiet()).unwrap();
    r.required_quotient(&quiet())
        .unwrap()
        .recheck(&i, &quiet())
        .unwrap();
}
#[test]
fn single_binding_match_and_let_preserve_tuple_projection_and_occurrence() {
    let (i, r) = table(
        "law required eq(c:Part):match c.pair{pair=>let n=pair.0 in ((n,pair.1)=(0,true));};",
    );
    assert!(r.is_complete());
    assert_eq!(r.positions(), &[fact("pair")]);
    assert_eq!(indicators(&r, &[0]), [0, 0, 1, 1].map(BigInt::from));
    assert_eq!(indicators(&r, &[1]), [1, 0, 1, 0].map(BigInt::from));
    assert_eq!(r.required_zero(), Some([1].as_slice()));
    let body = match r.columns[0].declaration.signature {
        Signature::Law { body, .. } => body,
        _ => panic!(),
    };
    let id = equation(&i, body, &quiet()).unwrap().unwrap();
    assert!(matches!(i.law().exprs()[body].kind, ExprKind::Match { .. }));
    assert!(matches!(
        i.law().exprs()[id].kind,
        ExprKind::Binary { op: BinOp::Eq, .. }
    ));
    assert_ne!(body, id);
    assert!(
        r.columns[0]
            .rows
            .iter()
            .all(|row| row.support.contains(&fact("pair")))
    );
    r.recheck(&i, &quiet()).unwrap();
}
#[test]
fn discarded_let_and_wildcard_match_inputs_remain_original_support_coordinates() {
    for body in [
        "law required eq(c:Part):let unused=c.quantity in c.pair=(0,true);",
        "law required eq(c:Part):match c.quantity{_=>c.pair=(0,true);};",
    ] {
        let (i, r) = table(body);
        assert!(r.is_complete());
        assert_eq!(r.positions(), &[fact("pair"), fact("quantity")]);
        assert_eq!(r.domain().len(), 8);
        assert_eq!(
            indicators(&r, &[0]),
            [0, 0, 0, 0, 1, 1, 1, 1].map(BigInt::from)
        );
        assert_eq!(
            indicators(&r, &[1]),
            [1, 1, 0, 0, 1, 1, 0, 0].map(BigInt::from)
        );
        for row in r.columns()[0].rows() {
            assert!(row.support.contains(&fact("pair")));
            assert!(row.support.contains(&fact("quantity")));
        }
        r.recheck(&i, &quiet()).unwrap();
    }
}
#[test]
fn helper_let_reuses_same_field_and_original_scoped_evaluation() {
    let (i, r) = table(
        "view read(c:Part):Fp(2)=c.quantity;law required eq(c:Part):let n=read(c) in let twice=n+n in twice=0;",
    );
    assert!(r.is_complete());
    assert_eq!(r.positions(), &[fact("quantity")]);
    assert_eq!(r.domain().len(), 2);
    assert_eq!(indicators(&r, &[]), [0, 0].map(BigInt::from));
    for row in r.columns[0].rows() {
        assert_eq!(
            row.operands.as_ref().unwrap().1,
            Some(Scalar::Fp {
                modulus: "2".into(),
                value: 0.into()
            })
        );
        assert!(row.support.contains(&fact("quantity")));
    }
    r.recheck(&i, &quiet()).unwrap();
}
#[test]
fn unknown_binding_match_retains_typed_uncomputed_operands_then_enumerates_all_values() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required eq(c:Part):match c.third{n=>n=0;};",
    );
    let e = Environment::new(&i, &quiet()).unwrap();
    *e.state.primitive_reads.borrow_mut() = Some(BTreeSet::new());
    let decl = &i.law().declarations()["Selected.eq"];
    let bindings = vec![("c".into(), subject("p"))];
    let p = probe(&e, decl, &bindings, 0).unwrap();
    assert_eq!(p.row.predicate, None);
    assert_eq!(p.row.indicator, None);
    assert_eq!(p.row.operands, Some((Type::Fp("3".into()), None, None)));
    let cs = p.row.components.unwrap();
    assert_eq!(cs.len(), 1);
    assert_eq!(cs[0].left, None);
    assert_eq!(cs[0].right, None);
    assert_eq!(cs[0].indicator, None);
    assert!(
        e.state
            .primitive_reads
            .borrow()
            .as_ref()
            .unwrap()
            .contains(&fact("third"))
    );
    assert!(!p.row.support.contains(&fact("third")));
    let r = finite_law_family_valuations(&i, &selected(), &quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(r.positions(), &[fact("third")]);
    assert_eq!(r.domain().len(), 3);
    assert_eq!(r.observed_point(), None);
    assert_eq!(indicators(&r, &[]), [0, 1, 1].map(BigInt::from));
    r.recheck(&i, &quiet()).unwrap();
}
#[test]
fn failed_owned_condition_in_unused_let_is_not_a_successful_zero_component() {
    let i = fixture::with_body(
        fixture::MAP,
        "view accept(r:Root,c:Part[r]):Bool=true;law required eq(r:Root,c:Part):let unused=accept(r,c) in c.pair=(0,true);",
    );
    let bindings = vec![("r".into(), subject("r2")), ("c".into(), subject("p"))];
    let r =
        finite_law_family_valuations(&i, &[("Selected.eq".into(), bindings)], &quiet()).unwrap();
    assert!(r.domain_complete());
    assert_eq!(r.positions(), &[fact("owner"), fact("pair")]);
    assert_eq!(r.domain().len(), 8);
    assert_eq!(r.state(), &FiniteLawState::ConditionFailed);
    assert_eq!(r.required_zero(), None);
    assert_eq!(r.domain()[0][0], subject("r2"));
    assert_eq!(r.domain()[4][0], subject("root"));
    for (point, row) in r.columns[0].rows().iter().enumerate() {
        assert_eq!(row.condition_failed, point >= 4);
        assert!(row.support.contains(&fact("owner")));
        assert!(row.support.contains(&fact("pair")));
        assert_eq!(row.components.as_ref().unwrap().len(), 2);
        if point >= 4 {
            assert_eq!(row.indicator, None);
            assert!(
                row.components
                    .as_ref()
                    .unwrap()
                    .iter()
                    .all(|c| c.indicator.is_none())
            );
        }
    }
    assert!(r.required_generators(&quiet()).is_err());
    assert!(r.required_quotient(&quiet()).is_err());
    r.recheck(&i, &quiet()).unwrap();
}
#[test]
fn pending_owned_condition_in_unused_let_does_not_certify_equal_components() {
    let owner_atom = r#"{"id":"op","subject":"p","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},"#;
    assert_eq!(fixture::MAP.matches(owner_atom).count(), 1);
    let map = fixture::MAP.replacen(owner_atom, "", 1);
    let i = fixture::with_body(
        &map,
        "view accept(r:Root,c:Part[r]):Bool=true;law required eq(r:Root,c:Part):let unused=accept(r,c) in c.pair=(0,true);",
    );
    let e = Environment::new(&i, &quiet()).unwrap();
    *e.state.primitive_reads.borrow_mut() = Some(BTreeSet::new());
    let bindings = vec![("r".into(), subject("r2")), ("c".into(), subject("p"))];
    let p = probe(&e, &i.law().declarations()["Selected.eq"], &bindings, 0).unwrap();
    assert!(p.admissible);
    assert!(!p.row.condition_failed);
    assert_eq!(p.row.guard, Some(true));
    assert_eq!(p.row.predicate, None);
    assert_eq!(p.row.indicator, None);
    let cs = p.row.components.as_ref().unwrap();
    assert_eq!(cs.len(), 2);
    assert!(cs.iter().all(|c| c.equal == Some(true)));
    assert!(cs.iter().all(|c| c.indicator.is_none()));
    assert!(
        e.state
            .primitive_reads
            .borrow()
            .as_ref()
            .unwrap()
            .contains(&fact("owner"))
    );
}
#[test]
fn different_match_cases_keep_whole_condition_without_identifying_component_occurrences() {
    let (i, r) = table(
        "law required eq(c:Part):match c.choice{Left(n)=>(n,true)=(0,true);Right(n)=>(n,false)=(0,true);};",
    );
    assert!(r.is_complete());
    assert_eq!(r.positions(), &[fact("choice")]);
    assert_eq!(r.domain().len(), 4);
    assert_eq!(r.columns[0].equation_type, None);
    assert!(
        r.columns[0]
            .rows
            .iter()
            .all(|row| row.operands.is_none() && row.components.is_none())
    );
    assert_eq!(
        r.integer_function(0, None, &quiet()).unwrap().values(),
        [0, 1, 1, 1].map(BigInt::from)
    );
    assert!(r.integer_function(0, Some(&[0]), &quiet()).is_err());
    assert_eq!(r.required_generators(&quiet()).unwrap().len(), 1);
    r.recheck(&i, &quiet()).unwrap();
}
#[test]
fn empty_d_retains_lexical_tuple_schema_and_original_required_generators() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required eq(r:Root,c:Part[r]):let pair=(true,false) in match pair{x=>x=(true,false);};",
    );
    let bind = |name: &str| vec![("r".into(), subject(name)), ("c".into(), subject("p"))];
    let r = finite_law_family_valuations(
        &i,
        &[
            ("Selected.eq".into(), bind("root")),
            ("Selected.eq".into(), bind("r2")),
        ],
        &quiet(),
    )
    .unwrap();
    assert!(r.is_complete());
    assert!(r.domain().is_empty());
    assert_eq!(
        r.columns[0].equation_type,
        Some(Type::Tuple(vec![Type::Bool, Type::Bool]))
    );
    let gs = r.required_generators(&quiet()).unwrap();
    assert_eq!(
        gs.iter()
            .map(|g| (g.column(), g.component().unwrap().to_vec()))
            .collect::<Vec<_>>(),
        [(0, vec![0]), (0, vec![1]), (1, vec![0]), (1, vec![1])]
    );
    assert!(gs.iter().all(|g| g.value().values().is_empty()));
    r.required_quotient(&quiet())
        .unwrap()
        .recheck(&i, &quiet())
        .unwrap();
    r.recheck(&i, &quiet()).unwrap();
}
#[test]
fn lexical_recheck_rejects_operands_component_schema_support_and_zero_coordinate_mutations() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required eq(c:Part):let pair=c.pair in match pair{x=>x=(0,true);};",
    );
    for change in 0..8 {
        let mut r = finite_law_family_valuations(&i, &selected(), &quiet()).unwrap();
        match change {
            0 => r.columns[0].equation_type = Some(Type::Bool),
            1 => r.columns[0].rows[0].operands = None,
            2 => r.columns[0].rows[0].operands.as_mut().unwrap().1 = None,
            3 => r.columns[0].rows[0].components.as_mut().unwrap()[0].path = vec![1],
            4 => r.columns[0].rows[0].support.clear(),
            5 => r.columns[0].rows[0].scope = Scope::default(),
            6 => r.columns[0].rows[0].components.as_mut().unwrap()[0].indicator = Some(1.into()),
            _ => r.required_zero = Some(vec![]),
        }
        assert!(r.recheck(&i, &quiet()).is_err(), "change={change}");
    }
}
#[test]
fn lexical_fixed_stops_preserve_finished_source_table_and_never_certify_partial_family() {
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    let i = fixture::with_body(
        fixture::MAP,
        "law required eq(c:Part):let pair=c.pair in match pair{x=>x=(0,true);};",
    );
    let completed = finite_law_family_valuations(&i, &selected(), &quiet()).unwrap();
    let control = |at: usize, signal: Signal| {
        let seen = Rc::new(Cell::new(0));
        let visits = seen.clone();
        let calls = Rc::new(Cell::new(0));
        let samples = calls.clone();
        (
            Control::new(move |cp| {
                samples.set(samples.get() + 1);
                if cp == Checkpoint::FiniteLawOperand {
                    visits.set(visits.get() + 1);
                }
                (visits.get() >= at).then_some(signal)
            }),
            seen,
            calls,
        )
    };
    let (c, visits, _) = control(usize::MAX, Signal::Int);
    finite_law_family_valuations(&i, &selected(), &c).unwrap();
    let total = visits.get();
    assert!(total > 3);
    for at in [1, total / 2, total] {
        for signal in [Signal::Int, Signal::Term] {
            let (c, _, calls) = control(at, signal);
            let f = finite_law_family_valuations(&i, &selected(), &c)
                .err()
                .expect("停止が成功");
            assert!(matches!(f.cause,ValidationFailure::Stop(ref s) if s==&signal));
            if let Some(partial) = f.partial {
                assert!(!partial.is_complete());
                assert_eq!(partial.required_zero(), None);
                for col in partial.columns() {
                    for (index, row) in col.rows().iter().enumerate() {
                        assert_eq!(row.point, index);
                    }
                }
            }
            let before = calls.get();
            assert_eq!(c.checkpoint(Checkpoint::FiniteLawOperand), Err(signal));
            assert_eq!(before, calls.get());
            completed.recheck(&i, &quiet()).unwrap();
            assert_eq!(completed.required_zero(), Some([1].as_slice()));
        }
    }
}
