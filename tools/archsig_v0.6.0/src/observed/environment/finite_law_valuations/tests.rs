use super::*;
use crate::control::Control;
#[allow(dead_code)]
mod fixture {
    include!("../../../../tests/common/primitive_valuation_data.rs");
}
fn quiet() -> Control {
    Control::unlimited()
}
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
fn fp(n: u8) -> Scalar {
    Scalar::Fp {
        modulus: "2".into(),
        value: n.into(),
    }
}
fn position(s: &str, f: &str) -> Fact {
    Fact {
        snapshot: "v".into(),
        subject: s.into(),
        field: Some(format!("Pattern.Part.{f}")),
        atom: None,
    }
}
fn bound() -> Vec<(String, Scalar)> {
    vec![("c".into(), subject("p"))]
}
#[test]
fn bool_fp_guard_uses_four_shared_points_and_integer_indicators() {
    let i = fixture::inputs();
    let before = i.sources().clone();
    let r = finite_law_valuations(&i, "Selected.guarded", &bound(), &mut quiet()).unwrap();
    assert!(r.is_complete());
    assert!(r.domain_complete());
    assert_eq!(
        r.positions(),
        &[position("p", "flag"), position("p", "quantity")]
    );
    assert_eq!(
        r.domain(),
        &[
            vec![Scalar::Bool(false), fp(0)],
            vec![Scalar::Bool(false), fp(1)],
            vec![Scalar::Bool(true), fp(0)],
            vec![Scalar::Bool(true), fp(1)]
        ]
    );
    assert_eq!(
        r.rows()
            .iter()
            .map(|p| p.indicator.clone())
            .collect::<Vec<_>>(),
        vec![
            Some(0.into()),
            Some(0.into()),
            Some(0.into()),
            Some(1.into())
        ]
    );
    assert_eq!(r.observed_point(), Some(2));
    for (index, row) in r.rows().iter().enumerate() {
        assert_eq!(row.point, index);
        assert_eq!(row.guard, Some(index >= 2));
        assert_eq!(row.predicate, Some(index % 2 == 0));
        assert!(row.scope.assignments);
        assert!(row.support.iter().all(|f| f.atom.is_none()));
        assert_eq!(row.operands.as_ref().unwrap().0, Type::Fp("2".into()));
    }
    r.recheck(&i, &mut quiet()).unwrap();
    assert_eq!(i.sources(), &before);
}
#[test]
fn candidate_branches_and_dynamic_references_expand_the_shared_positions() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required branched(c:Part):(if c.flag then c.quantity else c.link.quantity)=0;",
    );
    let r = finite_law_valuations(&i, "Selected.branched", &bound(), &mut quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(
        r.positions(),
        &[
            position("p", "flag"),
            position("p", "link"),
            position("p", "quantity"),
            position("q", "quantity")
        ]
    );
    assert_eq!(r.domain().len(), 16);
    for (values, row) in r.domain().iter().zip(r.rows()) {
        let Scalar::Bool(flag) = &values[0] else {
            panic!()
        };
        let Scalar::Subject {
            subject: target, ..
        } = &values[1]
        else {
            panic!()
        };
        let value = if *flag || target == "p" {
            &values[2]
        } else {
            &values[3]
        };
        let equal = value == &fp(0);
        assert_eq!(row.predicate, Some(equal));
        assert_eq!(row.indicator, Some(BigInt::from(!equal as u8)));
    }
    assert_eq!(
        r.rows()
            .iter()
            .filter(|p| p.indicator == Some(1.into()))
            .count(),
        8
    );
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn missing_finite_field_is_enumerated_without_an_observed_point() {
    let map=fixture::MAP.replace(r#"{"id":"xp","subject":"p","field":"Pattern.Part.quantity","value":"0","origin":"model"},"# ,"");
    let i = fixture::with_body(&map, "law required value(c:Part):c.quantity=0;");
    let before = i.sources().clone();
    let r = finite_law_valuations(&i, "Selected.value", &bound(), &mut quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(r.domain(), &[vec![fp(0)], vec![fp(1)]]);
    assert_eq!(r.observed_point(), None);
    assert_eq!(r.rows()[0].indicator, Some(0.into()));
    assert_eq!(r.rows()[1].indicator, Some(1.into()));
    assert_eq!(i.sources(), &before);
}
#[test]
fn shared_occurrences_reuse_one_position_and_a_constant_has_one_empty_assignment() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required shared(c:Part):(c.quantity+1)+c.quantity=1;law required constant():true;",
    );
    let r = finite_law_valuations(&i, "Selected.shared", &bound(), &mut quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(r.positions(), &[position("p", "quantity")]);
    assert_eq!(r.domain().len(), 2);
    assert!(
        r.rows()
            .iter()
            .all(|p| p.predicate == Some(true) && p.indicator == Some(0.into()))
    );
    let c = finite_law_valuations(&i, "Selected.constant", &[], &mut quiet()).unwrap();
    assert!(c.is_complete());
    assert_eq!(c.domain(), &[Vec::<Scalar>::new()]);
    assert_eq!(c.observed_point(), Some(0));
    assert_eq!(c.rows()[0].indicator, Some(0.into()));
}
#[test]
fn known_infinite_type_does_not_become_a_singleton_candidate_domain() {
    let map = fixture::MAP.replace("\"atoms\":[", r#""atoms":[{"id":"integer-p","subject":"p","field":"Pattern.Part.integer","value":"7","origin":"model"},"#);
    let i = fixture::with_body(&map, "law required integer(c:Part):c.integer=c.integer;");
    let r = finite_law_valuations(&i, "Selected.integer", &bound(), &mut quiet()).unwrap();
    assert!(!r.is_complete());
    assert!(!r.domain_complete());
    assert!(r.rows().is_empty());
    assert!(
        matches!(r.state(),FiniteLawState::OutsideFinite{position:p,ty:Type::Z} if p==&position("p","integer"))
    );
}
#[test]
fn invalid_binding_names_types_references_and_non_law_selections_are_rejected() {
    let i = fixture::inputs();
    for bindings in [
        vec![],
        vec![("c".into(), subject("p")), ("c".into(), subject("p"))],
        vec![("other".into(), subject("p"))],
        vec![("c".into(), Scalar::Bool(true))],
        vec![("c".into(), subject("absent"))],
    ] {
        assert!(finite_law_valuations(&i, "Selected.guarded", &bindings, &mut quiet()).is_err());
    }
    assert!(finite_law_valuations(&i, "Selected.value", &bound(), &mut quiet()).is_err());
    assert!(finite_law_valuations(&i, "Selected.absent", &bound(), &mut quiet()).is_err());
}

#[test]
fn helper_reads_are_shared_and_false_laws_do_not_prune_the_domain() {
    let i = fixture::with_body(
        fixture::MAP,
        "view next(c:Part):Fp(2)=c.quantity+1;law required helper(c:Part):next(c)=c.quantity;law required absent(c:Part):false;",
    );
    let r = finite_law_valuations(&i, "Selected.helper", &bound(), &mut quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(r.positions(), &[position("p", "quantity")]);
    assert_eq!(r.domain(), &[vec![fp(0)], vec![fp(1)]]);
    assert!(r.rows().iter().all(|row| row.indicator == Some(1.into())));
    let r = finite_law_valuations(&i, "Selected.absent", &bound(), &mut quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(r.domain(), &[Vec::<Scalar>::new()]);
    assert_eq!(r.rows()[0].indicator, Some(1.into()));
}

#[test]
fn helper_condition_failure_keeps_the_candidate_without_zero_filling() {
    let i = fixture::with_body(
        fixture::MAP,
        "view accepts(r:Root,c:Part[r]):Bool=true;law required checked(r:Root,c:Part):accepts(r,c);",
    );
    let r = finite_law_valuations(
        &i,
        "Selected.checked",
        &[("r".into(), subject("root")), ("c".into(), subject("p"))],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.state(), &FiniteLawState::ConditionFailed);
    assert!(!r.is_complete());
    assert!(r.domain_complete());
    assert_eq!(r.positions(), &[position("p", "owner")]);
    assert_eq!(r.domain().len(), 2);
    assert_eq!(r.rows().len(), 2);
    let failed = r
        .rows()
        .iter()
        .filter(|row| row.condition_failed)
        .collect::<Vec<_>>();
    assert_eq!(failed.len(), 1);
    assert_eq!(failed[0].indicator, None);
    assert!(r.rows().iter().any(|row| row.indicator == Some(0.into())));
    r.recheck(&i, &mut quiet()).unwrap();
}

#[test]
fn candidate_path_dependency_discovery_retains_original_nonfinite_list_position() {
    mod paths {
        use crate as archsig;
        include!("../../../../tests/common/internal_paths.rs");
    }
    use crate::input::{InputSources, check_inputs};
    let original = paths::input("normal", "finite-law");
    let law = String::from_utf8(original.law().bytes().to_vec())
        .unwrap()
        .replace(
            "law required prior():false;",
            "law required prior(e:Hop):path(e)=path(e);",
        );
    let inputs = check_inputs(
        InputSources::from_bytes(
            original
                .definitions()
                .iter()
                .map(|d| d.bytes().to_vec())
                .collect(),
            law.into_bytes(),
            original.archmap().bytes().to_vec(),
        ),
        &mut quiet(),
    )
    .unwrap();
    let binding = Scalar::Subject {
        snapshot: "v".into(),
        subject: "e".into(),
        entity: "Paths.Hop".into(),
    };
    let r = finite_law_valuations(
        &inputs,
        "Walk.prior",
        &[("e".into(), binding)],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.state(), &FiniteLawState::OutsideFinite {
        position: Fact { snapshot: "v".into(), subject: "p".into(), field: Some("Paths.Node.links".into()), atom: None },
        ty: Type::List(Box::new(Type::Ref("Paths.Node".into()))),
    });
    assert!(!r.is_complete());
    assert!(!r.domain_complete());
    assert!(r.domain().is_empty());
    assert!(r.rows().is_empty());
    r.recheck(&inputs, &mut quiet()).unwrap();
}

#[test]
fn owned_map_candidates_keep_all_ten_total_functions_over_moving_families() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required table(c:Part):c.ownedtable=c.ownedtable;",
    );
    let r = finite_law_valuations(&i, "Selected.table", &bound(), &mut quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(
        r.positions(),
        &[
            position("p", "ownedtable"),
            position("p", "owner"),
            position("q", "owner")
        ]
    );
    assert_eq!(r.domain().len(), 10);
    assert_eq!(r.observed_point(), None);
    for point in r.domain() {
        let Scalar::Map { pairs, .. } = &point[0] else {
            panic!()
        };
        let family = if point[1] == point[2] {
            vec![subject("p"), subject("q")]
        } else {
            vec![subject("p")]
        };
        assert_eq!(
            pairs.iter().map(|(k, _)| k.clone()).collect::<Vec<_>>(),
            family
        );
        assert!(pairs.iter().all(|(_, v)| family.contains(v)));
    }
    assert!(r.rows().iter().all(|row| row.indicator == Some(0.into())));
    r.recheck(&i, &mut quiet()).unwrap();
}

#[test]
fn unique_empty_list_and_map_have_one_value_without_observation_promotion() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required empty(c:Part):c.empty=c.empty;law required table(c:Part):c.emptytable=c.emptytable;",
    );
    for name in ["empty", "table"] {
        let r =
            finite_law_valuations(&i, &format!("Selected.{name}"), &bound(), &mut quiet()).unwrap();
        assert!(r.is_complete());
        assert_eq!(r.domain().len(), 1);
        assert_eq!(r.domain()[0].len(), 1);
        match &r.domain()[0][0] {
            Scalar::List { items, .. } => assert!(items.is_empty()),
            Scalar::Map { pairs, .. } => assert!(pairs.is_empty()),
            _ => panic!(),
        }
        assert_eq!(r.observed_point(), None);
        assert_eq!(r.rows()[0].predicate, Some(true));
        assert_eq!(r.rows()[0].indicator, Some(0.into()));
    }
}

#[test]
fn fixed_owned_binding_can_have_an_empty_admissible_domain() {
    let map=fixture::MAP.replace("\"atoms\":[",r#""atoms":[{"id":"table-p","subject":"p","field":"Pattern.Part.ownedtable","value":[[["v","p"],["v","p"]],[["v","q"],["v","q"]]],"origin":"model"},"#);
    let i = fixture::with_body(&map, "law required owned(r:Root,c:Part[r]):false;");
    let r = finite_law_valuations(
        &i,
        "Selected.owned",
        &[("r".into(), subject("r2")), ("c".into(), subject("p"))],
        &mut quiet(),
    )
    .unwrap();
    assert!(r.is_complete());
    assert!(r.domain_complete());
    assert_eq!(r.positions(), &[position("p", "owner")]);
    assert!(r.domain().is_empty());
    assert!(r.rows().is_empty());
    assert_eq!(r.observed_point(), None);
    r.recheck(&i, &mut quiet()).unwrap();
}

#[test]
fn recheck_rejects_changes_to_the_original_contract_domain_and_rows() {
    let i = fixture::inputs();
    let fresh = || finite_law_valuations(&i, "Selected.guarded", &bound(), &mut quiet()).unwrap();
    for change in 0..13 {
        let mut r = fresh();
        match change {
            0 => r.bindings[0].1 = subject("q"),
            1 => r.positions[0].subject = "q".into(),
            2 => r.types[0] = Type::Z,
            3 => {
                r.domain.pop();
            }
            4 => r.domain[0][0] = Scalar::Bool(true),
            5 => r.domain_complete = false,
            6 => r.observed_point = None,
            7 => r.rows[0].guard = Some(true),
            8 => r.rows[0].predicate = Some(false),
            9 => r.rows[0].indicator = Some(1.into()),
            10 => r.rows[0].operands = None,
            11 => r.rows[0].scope.assignments = false,
            12 => r.state = FiniteLawState::Pending,
            _ => unreachable!(),
        }
        assert!(r.recheck(&i, &mut quiet()).is_err(), "change={change}");
    }
    let other = fixture::with_body(
        fixture::MAP,
        "law required guarded(c:Part) when c.flag:c.quantity=1;",
    );
    assert!(fresh().recheck(&other, &mut quiet()).is_err());
}

#[test]
fn fixed_stops_leave_only_completed_rows_and_freeze_the_probe() {
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    fn control(
        point: Checkpoint,
        at: usize,
        signal: Signal,
    ) -> (Control, Rc<Cell<usize>>, Rc<Cell<usize>>) {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let calls = Rc::new(Cell::new(0));
        let sampled = calls.clone();
        (
            Control::new(move |p| {
                sampled.set(sampled.get() + 1);
                if p == point {
                    seen.set(seen.get() + 1)
                }
                (seen.get() >= at).then_some(signal)
            }),
            count,
            calls,
        )
    }
    let i = fixture::inputs();
    for point in [Checkpoint::FiniteLawDomain, Checkpoint::FiniteLawEvaluation] {
        let (mut c, count, _) = control(point, usize::MAX, Signal::Int);
        finite_law_valuations(&i, "Selected.guarded", &bound(), &mut c).unwrap();
        let total = count.get();
        assert!(total > 1);
        for at in [1, total] {
            for signal in [Signal::Int, Signal::Term] {
                let (mut c, _, calls) = control(point, at, signal);
                let failure = match finite_law_valuations(&i, "Selected.guarded", &bound(), &mut c)
                {
                    Err(f) => f,
                    Ok(_) => panic!("停止が成功になった"),
                };
                assert!(matches!(failure.cause,ValidationFailure::Stop(ref s) if s==&signal));
                let partial = failure.partial.unwrap();
                assert!(!partial.is_complete());
                // 完成フラグに到達しても、停止した実行全体を成功結果として返さない。
                if !partial.domain_complete() {
                    assert!(partial.rows().is_empty());
                }
                assert!(partial.rows().iter().all(|r| r.indicator.is_some()));
                let before = calls.get();
                assert_eq!(c.checkpoint(point), Err(signal));
                assert_eq!(calls.get(), before);
            }
        }
    }
}

#[test]
fn incomplete_non_owned_map_binding_must_be_rejected() {
    let i = fixture::with_body(fixture::MAP, "law required fixed(t:Map<Part,Part>):true;");
    let v = Scalar::Map {
        domain: Type::Ref("Pattern.Part".into()),
        codomain: Type::Ref("Pattern.Part".into()),
        pairs: vec![],
    };
    let r = finite_law_valuations(&i, "Selected.fixed", &[("t".into(), v)], &mut quiet());
    assert!(
        r.is_err(),
        "two registered Part subjects require two Map keys"
    );
}
#[test]
fn unregistered_path_binding_must_be_rejected() {
    let i = fixture::with_body(fixture::MAP, "law required fixed(p:Path<Part,Part>):true;");
    let v = Scalar::Path(Box::new(crate::observed::path_value::PathValue {
        reading: "Selected".into(),
        snapshot: "v".into(),
        subject: "absent".into(),
        entity: "Pattern.Part".into(),
        step: None,
    }));
    let r = finite_law_valuations(&i, "Selected.fixed", &[("p".into(), v)], &mut quiet());
    assert!(
        r.is_err(),
        "unregistered Path source cannot be a typed fixed binding"
    );
}

#[test]
fn single_key_map_binding_must_be_rejected() {
    let i = fixture::with_body(fixture::MAP, "law required fixed(t:Map<Part,Part>):t=t;");
    let v = Scalar::Map {
        domain: Type::Ref("Pattern.Part".into()),
        codomain: Type::Ref("Pattern.Part".into()),
        pairs: vec![(subject("p"), subject("q"))],
    };
    assert!(finite_law_valuations(&i, "Selected.fixed", &[("t".into(), v)], &mut quiet()).is_err());
}
#[test]
fn total_map_binding_is_accepted() {
    let i = fixture::with_body(fixture::MAP, "law required fixed(t:Map<Part,Part>):t=t;");
    let v = Scalar::Map {
        domain: Type::Ref("Pattern.Part".into()),
        codomain: Type::Ref("Pattern.Part".into()),
        pairs: vec![(subject("p"), subject("q")), (subject("q"), subject("p"))],
    };
    let r = finite_law_valuations(&i, "Selected.fixed", &[("t".into(), v)], &mut quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(r.rows()[0].indicator, Some(0.into()));
}
#[test]
fn later_comprehension_dependencies_must_not_be_pruned_by_stale_constraints() {
    let map=fixture::MAP.replace("\"atoms\":[",r#""atoms":[{"id":"table-p","subject":"p","field":"Pattern.Part.ownedtable","value":[[["v","p"],["v","p"]],[["v","q"],["v","q"]]],"origin":"model"},"#);
    let i = fixture::with_body(
        &map,
        "law required branched(r:Root,c:Part):count(set{c.ownedtable | x in list<Part>[c] where c.owner!=r})=0;",
    );
    let r = finite_law_valuations(
        &i,
        "Selected.branched",
        &[("r".into(), subject("root")), ("c".into(), subject("p"))],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(
        r.positions(),
        &[
            position("p", "ownedtable"),
            position("p", "owner"),
            position("q", "owner")
        ]
    );
    assert_eq!(r.domain().len(), 10);
    assert!(r.is_complete());
    for (point, row) in r.domain().iter().zip(r.rows()) {
        assert_eq!(
            row.indicator,
            Some(BigInt::from((point[1] != subject("root")) as u8))
        );
    }
}

#[test]
fn forged_term_body_binding_must_be_rejected() {
    let i = fixture::with_body(
        fixture::MAP,
        "view make():Term<(Fp(2))->Fp(2)> =fn(n:Fp(2))=>n+1;law required fixed(t:Term<(Fp(2))->Fp(2)>):t(0)=1;",
    );
    let Signature::View { body, .. } = &i.law().declarations["Selected.make"].signature else {
        panic!()
    };
    let mut term =
        crate::observed::term::Term::from_law(i.law(), i.sources().law().bytes(), *body, &quiet())
            .unwrap();
    term.body = "n+0".into();
    let r = finite_law_valuations(
        &i,
        "Selected.fixed",
        &[("t".into(), Scalar::Term(Box::new(term)))],
        &mut quiet(),
    );
    assert!(
        r.is_err(),
        "Term text and executable AST must agree in fixed bindings"
    );
}

#[test]
fn unused_term_parameters_keep_the_original_identifier_rules() {
    let i = fixture::with_body(
        fixture::MAP,
        "view make():Term<(Fp(2))->Fp(2)> =fn(n:Fp(2))=>1;law required fixed(t:Term<(Fp(2))->Fp(2)>):t(0)=1;",
    );
    let value = literal_term(&i, "Selected.make");
    let Scalar::Term(original) = &value else {
        panic!()
    };
    for name in [
        "if", "bad-name", "", "1name", "_name", "x.y", "count", "名前",
    ] {
        let mut term = (**original).clone();
        term.params[0].0 = name.into();
        assert!(term.check(&quiet()).is_err(), "{name:?}");
        let bindings = vec![("t".into(), Scalar::Term(Box::new(term)))];
        assert!(
            finite_law_valuations(&i, "Selected.fixed", &bindings, &mut quiet()).is_err(),
            "{name:?}"
        );
    }
    for name in ["n", "unused_2", "N"] {
        let mut term = (**original).clone();
        term.params[0].0 = name.into();
        term.check(&quiet()).unwrap();
        let r = finite_law_valuations(
            &i,
            "Selected.fixed",
            &[("t".into(), Scalar::Term(Box::new(term)))],
            &mut quiet(),
        )
        .unwrap();
        assert!(r.is_complete());
        assert_eq!(r.rows()[0].indicator, Some(0.into()));
    }
}

#[test]
fn nested_maps_keep_their_original_full_domain_check() {
    for (ty, wrap) in [
        ("Map<Part,Part>", 0),
        ("(Unit,Map<Part,Part>)", 1),
        ("List<Map<Part,Part>>", 2),
        ("Option<Map<Part,Part>>", 3),
    ] {
        let i = fixture::with_body(fixture::MAP, &format!("law required fixed(m:{ty}):true;"));
        for full in [false, true] {
            let map = Scalar::Map {
                domain: Type::Ref("Pattern.Part".into()),
                codomain: Type::Ref("Pattern.Part".into()),
                pairs: if full {
                    vec![(subject("p"), subject("p")), (subject("q"), subject("q"))]
                } else {
                    vec![]
                },
            };
            let value = match wrap {
                0 => map.clone(),
                1 => Scalar::Tuple(vec![Scalar::Unit, map.clone()]),
                2 => Scalar::List {
                    element: map.ty(),
                    items: vec![map.clone()],
                },
                _ => Scalar::Option {
                    element: map.ty(),
                    value: Some(Box::new(map.clone())),
                },
            };
            let result =
                finite_law_valuations(&i, "Selected.fixed", &[("m".into(), value)], &mut quiet());
            assert_eq!(result.is_ok(), full, "{ty}, full={full}");
        }
    }
}

fn literal_term(i: &CheckedInputs, name: &str) -> Scalar {
    let Signature::View { body, .. } = &i.law().declarations[name].signature else {
        panic!()
    };
    Scalar::Term(Box::new(
        crate::observed::term::Term::from_law(i.law(), i.sources().law().bytes(), *body, &quiet())
            .unwrap(),
    ))
}
#[test]
fn checked_term_bindings_reparse_in_the_original_reading_and_nested_containers() {
    let body = format!(
        "{}law required fixed(t:Term<(Fp(2))->Fp(2)>):t(0)=1;law required nested(ts:List<Term<(Fp(2))->Fp(2)>>):true;",
        fixture::BODY
    );
    let i = fixture::with_body(fixture::MAP, &body);
    for name in ["Selected.literal", "Selected.complex"] {
        let value = literal_term(&i, name);
        let r = finite_law_valuations(
            &i,
            "Selected.fixed",
            &[("t".into(), value.clone())],
            &mut quiet(),
        )
        .unwrap();
        assert!(r.is_complete());
        assert_eq!(r.rows()[0].indicator, Some(0.into()));
        let list = Scalar::List {
            element: value.ty(),
            items: vec![value.clone()],
        };
        assert!(
            finite_law_valuations(&i, "Selected.nested", &[("ts".into(), list)], &mut quiet())
                .unwrap()
                .is_complete()
        );
        let Scalar::Term(term) = &value else { panic!() };
        let mut changed = (**term).clone();
        changed.body = "make()".into();
        let bad = Scalar::List {
            element: value.ty(),
            items: vec![Scalar::Term(Box::new(changed))],
        };
        assert!(
            finite_law_valuations(&i, "Selected.nested", &[("ts".into(), bad)], &mut quiet())
                .is_err()
        );
    }
}

#[test]
fn closed_term_keeps_its_checked_meaning_across_readings() {
    let body = format!(
        "{}}}reading Closed{{law required fixed(t:Term<(Fp(2))->Fp(2)>):t(0)=1;",
        fixture::BODY
    );
    let i = fixture::with_body(fixture::MAP, &body);
    let value = literal_term(&i, "Selected.complex");
    let r =
        finite_law_valuations(&i, "Closed.fixed", &[("t".into(), value)], &mut quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(r.rows()[0].indicator, Some(0.into()));
}

#[test]
fn definition_term_binding_remains_valid_without_a_law_vocabulary_import() {
    use crate::input::{InputSources, check_inputs};
    let donor = fixture::inputs();
    let value = literal_term(&donor, "Selected.complex");
    let i=check_inputs(InputSources::from_bytes(donor.sources().definitions().iter().map(|d|d.bytes().to_vec()).collect(),b"law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Closed{law required fixed(t:Term<(Fp(2))->Fp(2)>):t(0)=1;}".to_vec(),donor.sources().archmap().bytes().to_vec()),&mut quiet()).unwrap();
    let r =
        finite_law_valuations(&i, "Closed.fixed", &[("t".into(), value)], &mut quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(r.rows()[0].indicator, Some(0.into()));
}

#[test]
fn term_binding_reparse_stops_before_publishing_and_freezes_the_probe() {
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    fn controlled(at: usize, signal: Signal) -> (Control, Rc<Cell<usize>>, Rc<Cell<usize>>) {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let calls = Rc::new(Cell::new(0));
        let all = calls.clone();
        (
            Control::new(move |point| {
                all.set(all.get() + 1);
                if point == Checkpoint::ArchMapTerm {
                    seen.set(seen.get() + 1);
                }
                (seen.get() >= at).then_some(signal)
            }),
            count,
            calls,
        )
    }
    let i = fixture::with_body(
        fixture::MAP,
        "view make():Term<(Fp(2))->Fp(2)> =fn(n:Fp(2))=>n+1;law required fixed(t:Term<(Fp(2))->Fp(2)>):t(0)=1;",
    );
    let bindings = vec![("t".into(), literal_term(&i, "Selected.make"))];
    let (mut c, count, _) = controlled(usize::MAX, Signal::Int);
    assert!(
        finite_law_valuations(&i, "Selected.fixed", &bindings, &mut c)
            .unwrap()
            .is_complete()
    );
    let total = count.get();
    assert!(total > 1);
    for at in [1, total] {
        for signal in [Signal::Int, Signal::Term] {
            let (mut c, _, calls) = controlled(at, signal);
            let failure = match finite_law_valuations(&i, "Selected.fixed", &bindings, &mut c) {
                Err(f) => f,
                Ok(_) => panic!("中断後に完成表を返した"),
            };
            assert!(matches!(failure.cause,ValidationFailure::Stop(ref s) if s==&signal));
            let partial = failure.partial.unwrap();
            assert!(!partial.is_complete());
            assert!(partial.rows().is_empty());
            let before = calls.get();
            assert_eq!(c.checkpoint(Checkpoint::ArchMapTerm), Err(signal));
            assert_eq!(calls.get(), before);
        }
    }
}

#[test]
fn registered_identity_and_reconstructed_path_bindings_are_accepted_but_forged_actions_are_not() {
    mod paths {
        use crate as archsig;
        include!("../../../../tests/common/internal_paths.rs");
    }
    use crate::input::{InputSources, check_inputs};
    let original = paths::input("normal", "fixed-path");
    let law = String::from_utf8(original.law().bytes().to_vec())
        .unwrap()
        .replace(
            "law required prior():false;",
            "law required prior(p:Path<Node,Node>):p=p;",
        );
    let inputs = check_inputs(
        InputSources::from_bytes(
            original
                .definitions()
                .iter()
                .map(|d| d.bytes().to_vec())
                .collect(),
            law.into_bytes(),
            original.archmap().bytes().to_vec(),
        ),
        &mut quiet(),
    )
    .unwrap();
    let e = Environment::new(&inputs, &mut quiet()).unwrap();
    let Signature::View { body, .. } = &inputs.law().declarations["Walk.step"].signature else {
        panic!()
    };
    let generator = Scalar::Subject {
        snapshot: "v".into(),
        subject: "e".into(),
        entity: "Paths.Hop".into(),
    };
    let value = e.internal_path(*body, &[generator]).unwrap().value.unwrap();
    let identity = Scalar::Path(Box::new(crate::observed::path_value::PathValue {
        reading: "Walk".into(),
        snapshot: "v".into(),
        subject: "p".into(),
        entity: "Paths.Node".into(),
        step: None,
    }));
    for value in [identity, value.clone()] {
        let r = finite_law_valuations(&inputs, "Walk.prior", &[("p".into(), value)], &mut quiet())
            .unwrap();
        assert!(r.is_complete());
        assert_eq!(r.rows()[0].indicator, Some(0.into()));
    }
    let Scalar::Path(path) = &value else { panic!() };
    let mut forged = (**path).clone();
    let step = forged.step.as_mut().unwrap();
    step.images[0] = step.carrier[0].clone();
    // 元と違う全域作用を、同じ生成語の値として渡さない。
    if step.images == path.step.as_ref().unwrap().images {
        step.images[0] = step.carrier[1].clone();
    }
    assert!(
        finite_law_valuations(
            &inputs,
            "Walk.prior",
            &[("p".into(), Scalar::Path(Box::new(forged)))],
            &mut quiet()
        )
        .is_err()
    );
}

fn family_selection(
    items: &[(&str, Vec<(String, Scalar)>)],
) -> Vec<(String, Vec<(String, Scalar)>)> {
    items
        .iter()
        .map(|(n, b)| (format!("Selected.{n}"), b.clone()))
        .collect()
}
fn family_indicators(r: &FiniteLawFamilyValuations, column: usize) -> Vec<i32> {
    r.columns()[column]
        .rows()
        .iter()
        .map(|p| {
            if p.indicator == Some(0.into()) {
                0
            } else if p.indicator == Some(1.into()) {
                1
            } else {
                panic!("未確定の指示関数")
            }
        })
        .collect()
}
#[test]
fn family_shares_one_coordinate_and_keeps_contradictory_required_laws() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required zero(c:Part):c.quantity=0;law required one(c:Part):c.quantity=1;",
    );
    let selected = family_selection(&[("zero", bound()), ("one", bound())]);
    let r = finite_law_family_valuations(&i, &selected, &mut quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(r.positions(), &[position("p", "quantity")]);
    assert_eq!(r.types(), &[Type::Fp("2".into())]);
    assert_eq!(r.domain(), &[vec![fp(0)], vec![fp(1)]]);
    assert_eq!(r.observed_point(), Some(0));
    assert_eq!(family_indicators(&r, 0), vec![0, 1]);
    assert_eq!(family_indicators(&r, 1), vec![1, 0]);
    assert_eq!(r.required_zero(), Some([].as_slice()));
    assert!(r.columns().iter().all(|q| q.required()));
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn family_guard_and_optional_law_use_integer_functions_on_the_same_four_points() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required guarded(c:Part) when c.flag:c.quantity=0;law optional other(c:Part):c.quantity=1;",
    );
    let selected = family_selection(&[("guarded", bound()), ("other", bound())]);
    let r = finite_law_family_valuations(&i, &selected, &mut quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(
        r.domain(),
        &[
            vec![Scalar::Bool(false), fp(0)],
            vec![Scalar::Bool(false), fp(1)],
            vec![Scalar::Bool(true), fp(0)],
            vec![Scalar::Bool(true), fp(1)]
        ]
    );
    assert_eq!(family_indicators(&r, 0), vec![0, 0, 0, 1]);
    assert_eq!(family_indicators(&r, 1), vec![1, 0, 1, 0]);
    assert!(r.columns()[0].required());
    assert!(!r.columns()[1].required());
    assert_eq!(r.required_zero(), Some([0, 1, 2].as_slice()));
    assert_eq!(r.observed_point(), Some(2));
    for q in r.columns() {
        assert_eq!(q.bindings(), bound());
        for (point, row) in q.rows().iter().enumerate() {
            assert_eq!(row.point, point);
            let (ty, a, b) = row.operands.as_ref().unwrap();
            assert_eq!(ty, &Type::Fp("2".into()));
            assert_eq!(a.as_ref(), Some(&r.domain()[point][1]));
            assert!(b.is_some());
            assert!(row.scope.assignments);
            assert!(row.support.iter().all(|f| f.atom.is_none()));
        }
    }
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn family_independent_fields_form_one_product_and_same_law_bindings_stay_distinct() {
    let i = fixture::with_body(fixture::MAP, "law required zero(c:Part):c.quantity=0;");
    let selected = family_selection(&[
        ("zero", bound()),
        ("zero", vec![("c".into(), subject("q"))]),
    ]);
    let r = finite_law_family_valuations(&i, &selected, &mut quiet()).unwrap();
    assert_eq!(
        r.positions(),
        &[position("p", "quantity"), position("q", "quantity")]
    );
    assert_eq!(
        r.domain(),
        &[
            vec![fp(0), fp(0)],
            vec![fp(0), fp(1)],
            vec![fp(1), fp(0)],
            vec![fp(1), fp(1)]
        ]
    );
    assert_eq!(family_indicators(&r, 0), vec![0, 0, 1, 1]);
    assert_eq!(family_indicators(&r, 1), vec![0, 1, 0, 1]);
    assert_eq!(r.required_zero(), Some([0].as_slice()));
    assert_eq!(r.observed_point(), Some(1));
    assert_ne!(r.columns()[0].bindings(), r.columns()[1].bindings());
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn family_empty_selection_and_optional_false_keep_the_empty_assignment() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required no():false;law optional optionalNo():false;",
    );
    let empty = finite_law_family_valuations(&i, &[], &mut quiet()).unwrap();
    assert!(empty.is_complete());
    assert!(empty.domain_complete());
    assert!(empty.columns().is_empty());
    assert!(empty.positions().is_empty());
    assert_eq!(empty.domain(), &[Vec::<Scalar>::new()]);
    assert_eq!(empty.observed_point(), Some(0));
    assert_eq!(empty.required_zero(), Some([0].as_slice()));
    empty.recheck(&i, &mut quiet()).unwrap();
    let optional = finite_law_family_valuations(
        &i,
        &family_selection(&[("optionalNo", vec![])]),
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(family_indicators(&optional, 0), vec![1]);
    assert_eq!(optional.required_zero(), Some([0].as_slice()));
    let required =
        finite_law_family_valuations(&i, &family_selection(&[("no", vec![])]), &mut quiet())
            .unwrap();
    assert_eq!(required.domain(), &[Vec::<Scalar>::new()]);
    assert_eq!(family_indicators(&required, 0), vec![1]);
    assert_eq!(required.required_zero(), Some([].as_slice()));
}
#[test]
fn family_incompatible_fixed_owned_bindings_produce_empty_d_without_faking_a_point() {
    let i = fixture::with_body(fixture::MAP, "law required typed(r:Root,c:Part[r]):true;");
    let selected = family_selection(&[
        (
            "typed",
            vec![("r".into(), subject("root")), ("c".into(), subject("p"))],
        ),
        (
            "typed",
            vec![("r".into(), subject("r2")), ("c".into(), subject("p"))],
        ),
    ]);
    let r = finite_law_family_valuations(&i, &selected, &mut quiet()).unwrap();
    assert!(r.is_complete());
    assert!(r.domain_complete());
    assert_eq!(r.positions(), &[position("p", "owner")]);
    assert!(r.domain().is_empty());
    assert!(r.columns().iter().all(|q| q.rows().is_empty()));
    assert_eq!(r.observed_point(), None);
    assert_eq!(r.required_zero(), Some([].as_slice()));
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn family_missing_field_has_candidates_but_no_observed_point() {
    let map=fixture::MAP.replace(r#"{"id":"xp","subject":"p","field":"Pattern.Part.quantity","value":"0","origin":"model"},"#,"");
    let i = fixture::with_body(
        &map,
        "law required zero(c:Part):c.quantity=0;law optional flag(c:Part):c.flag;",
    );
    let r = finite_law_family_valuations(
        &i,
        &family_selection(&[("zero", bound()), ("flag", bound())]),
        &mut quiet(),
    )
    .unwrap();
    assert!(r.is_complete());
    assert_eq!(r.domain().len(), 4);
    assert_eq!(r.observed_point(), None);
    assert_eq!(r.required_zero(), Some([0, 2].as_slice()));
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn family_joint_discovery_keeps_delayed_reads_and_other_law_positions() {
    let map=fixture::MAP.replace("\"atoms\":[",r#""atoms":[{"id":"table-p","subject":"p","field":"Pattern.Part.ownedtable","value":[[["v","p"],["v","p"]],[["v","q"],["v","q"]]],"origin":"model"},"#);
    let i = fixture::with_body(
        &map,
        "law required branched(r:Root,c:Part):count(set{c.ownedtable | x in list<Part>[c] where c.owner!=r})=0;law optional other(c:Part):c.quantity=0;",
    );
    let r = finite_law_family_valuations(
        &i,
        &family_selection(&[
            (
                "branched",
                vec![("r".into(), subject("root")), ("c".into(), subject("p"))],
            ),
            ("other", bound()),
        ]),
        &mut quiet(),
    )
    .unwrap();
    assert!(r.is_complete());
    assert_eq!(
        r.positions(),
        &[
            position("p", "ownedtable"),
            position("p", "owner"),
            position("p", "quantity"),
            position("q", "owner")
        ]
    );
    assert_eq!(r.domain().len(), 20);
    assert_eq!(r.columns()[0].rows().len(), 20);
    assert_eq!(r.columns()[1].rows().len(), 20);
    for (point, values) in r.domain().iter().enumerate() {
        assert_eq!(
            r.columns()[0].rows()[point].predicate,
            Some(values[1] == subject("root"))
        );
        assert_eq!(
            r.columns()[1].rows()[point].predicate,
            Some(values[2] == fp(0))
        );
    }
    let expected = r
        .domain()
        .iter()
        .enumerate()
        .filter_map(|(p, v)| (v[1] == subject("root")).then_some(p))
        .collect::<Vec<_>>();
    assert_eq!(r.required_zero(), Some(expected.as_slice()));
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn family_preserves_selection_order_and_duplicate_occurrences() {
    let i = fixture::with_body(
        fixture::MAP,
        "law optional one(c:Part):c.quantity=1;law required zero(c:Part):c.quantity=0;",
    );
    let selected = family_selection(&[("one", bound()), ("zero", bound()), ("one", bound())]);
    let r = finite_law_family_valuations(&i, &selected, &mut quiet()).unwrap();
    assert_eq!(r.columns().len(), 3);
    assert_eq!(r.columns()[0].declaration(), r.columns()[2].declaration());
    assert_ne!(r.columns()[0].declaration(), r.columns()[1].declaration());
    assert_eq!(family_indicators(&r, 0), vec![1, 0]);
    assert_eq!(family_indicators(&r, 1), vec![0, 1]);
    assert_eq!(family_indicators(&r, 2), vec![1, 0]);
    assert_eq!(r.required_zero(), Some([0].as_slice()));
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn family_rejects_bad_declarations_bindings_and_unregistered_references() {
    let i = fixture::inputs();
    for name in ["Selected.absent", "Selected.value"] {
        assert!(finite_law_family_valuations(&i, &[(name.into(), bound())], &mut quiet()).is_err());
    }
    for bindings in [
        vec![],
        vec![("c".into(), subject("p")), ("c".into(), subject("q"))],
        vec![("x".into(), subject("p"))],
        vec![("c".into(), Scalar::Bool(false))],
        vec![("c".into(), subject("absent"))],
    ] {
        let selected = vec![
            ("Selected.guarded".into(), bound()),
            ("Selected.guarded".into(), bindings),
        ];
        assert!(finite_law_family_valuations(&i, &selected, &mut quiet()).is_err());
    }
}
#[test]
fn family_outside_finite_and_condition_failure_never_supply_zero_coordinates() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required infinite(c:Part):c.integer=0;law required finite(c:Part):c.quantity=0;",
    );
    let r = finite_law_family_valuations(
        &i,
        &family_selection(&[("infinite", bound()), ("finite", bound())]),
        &mut quiet(),
    )
    .unwrap();
    assert!(
        matches!(r.state(),FiniteLawState::OutsideFinite{position:p,ty:Type::Z} if p==&position("p","integer"))
    );
    assert!(!r.domain_complete());
    assert!(!r.is_complete());
    assert_eq!(r.required_zero(), None);
    assert!(r.columns().iter().all(|q| q.rows().is_empty()));
    r.recheck(&i, &mut quiet()).unwrap();
    let i = fixture::with_body(
        fixture::MAP,
        "view narrow(r:Root,x:Part):Part[r]=x;law required broken(r:Root,c:Part):narrow(r,c)=c;law required finite(c:Part):c.quantity=0;",
    );
    let r = finite_law_family_valuations(
        &i,
        &family_selection(&[
            (
                "broken",
                vec![("r".into(), subject("root")), ("c".into(), subject("p"))],
            ),
            ("finite", bound()),
        ]),
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.state(), &FiniteLawState::ConditionFailed);
    assert!(r.domain_complete());
    assert_eq!(r.required_zero(), None);
    assert!(r.columns()[0].rows().iter().any(|r| r.condition_failed));
    assert!(r.columns()[1].rows().iter().all(|r| r.indicator.is_some()));
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn family_recheck_rebuilds_all_columns_domain_and_required_zero() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required zero(c:Part):c.quantity=0;law optional one(c:Part):c.quantity=1;",
    );
    let selected = family_selection(&[("zero", bound()), ("one", bound())]);
    for change in 0..14 {
        let mut r = finite_law_family_valuations(&i, &selected, &mut quiet()).unwrap();
        match change {
            0 => r.positions.clear(),
            1 => r.types[0] = Type::Bool,
            2 => r.domain.pop().map(|_| ()).unwrap(),
            3 => r.domain[0][0] = fp(1),
            4 => r.domain_complete = false,
            5 => r.observed_point = Some(1),
            6 => r.state = FiniteLawState::Pending,
            7 => r.required_zero = Some(vec![1]),
            8 => r.columns.swap(0, 1),
            9 => r.columns[0].bindings[0].1 = subject("q"),
            10 => r.columns[0].rows[0].indicator = Some(1.into()),
            11 => r.columns[1].rows[0].point = 1,
            12 => r.columns[1].rows.pop().map(|_| ()).unwrap(),
            _ => r.columns[0].declaration = r.columns[1].declaration.clone(),
        }
        assert!(r.recheck(&i, &mut quiet()).is_err(), "change={change}");
    }
    let r = finite_law_family_valuations(&i, &selected, &mut quiet()).unwrap();
    let other = fixture::with_body(
        fixture::MAP,
        "law required zero(c:Part):c.quantity=1;law optional one(c:Part):c.quantity=1;",
    );
    assert!(r.recheck(&other, &mut quiet()).is_err());
}
#[test]
fn family_fixed_stops_preserve_only_completed_cells_and_freeze_probe() {
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    let i = fixture::with_body(
        fixture::MAP,
        "law required zero(c:Part):c.quantity=0;law optional one(c:Part):c.quantity=1;",
    );
    let selected = family_selection(&[("zero", bound()), ("one", bound())]);
    for point in [
        Checkpoint::FiniteLawSelection,
        Checkpoint::FiniteLawDomain,
        Checkpoint::FiniteLawEvaluation,
        Checkpoint::FiniteLawRequired,
    ] {
        let run = |at: usize, signal: Signal| {
            let seen = Rc::new(Cell::new(0));
            let visits = seen.clone();
            let calls = Rc::new(Cell::new(0));
            let sampled = calls.clone();
            (
                Control::new(move |p| {
                    sampled.set(sampled.get() + 1);
                    if p == point {
                        visits.set(visits.get() + 1);
                    }
                    (visits.get() >= at).then_some(signal)
                }),
                seen,
                calls,
            )
        };
        let (mut c, count, _) = run(usize::MAX, Signal::Int);
        finite_law_family_valuations(&i, &selected, &mut c).unwrap();
        let total = count.get();
        assert!(total > 1);
        for at in [1, total / 2, total] {
            for signal in [Signal::Int, Signal::Term] {
                let (mut c, _, calls) = run(at, signal);
                let failure = match finite_law_family_valuations(&i, &selected, &mut c) {
                    Err(f) => f,
                    Ok(_) => panic!("停止が成功"),
                };
                assert!(matches!(failure.cause,ValidationFailure::Stop(ref s) if s==&signal));
                if let Some(partial) = failure.partial {
                    assert!(!partial.is_complete());
                    assert_eq!(partial.required_zero(), None);
                    for q in partial.columns() {
                        if !partial.domain_complete() {
                            assert!(q.rows().is_empty());
                        }
                        for (p, row) in q.rows().iter().enumerate() {
                            assert_eq!(row.point, p);
                            assert!(row.indicator.is_some());
                        }
                    }
                }
                let before = calls.get();
                assert_eq!(c.checkpoint(point), Err(signal));
                assert_eq!(calls.get(), before);
            }
        }
    }
}

#[test]
fn scalar_equation_component_keeps_original_operand_and_whole_indicator() {
    let i = fixture::inputs();
    let r = finite_law_valuations(&i, "Selected.guarded", &bound(), &mut quiet()).unwrap();
    assert!(r.is_complete());
    for row in r.rows() {
        let cs = row.components.as_ref().unwrap();
        assert_eq!(cs.len(), 1);
        let p = &cs[0];
        assert!(p.path.is_empty());
        assert_eq!(p.ty, Type::Fp("2".into()));
        assert_eq!(p.left, row.operands.as_ref().unwrap().1);
        assert_eq!(p.right, row.operands.as_ref().unwrap().2);
        assert_eq!(p.equal, row.predicate);
        assert_eq!(p.indicator, row.indicator);
    }
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn tuple_guard_components_keep_zero_and_nonzero_separate_on_eight_shared_points() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required pair(c:Part) when c.flag:c.pair=(0,true);law optional no():false;",
    );
    let selected = family_selection(&[("pair", bound()), ("no", vec![])]);
    let r = finite_law_family_valuations(&i, &selected, &mut quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(
        r.positions(),
        &[position("p", "flag"), position("p", "pair")]
    );
    assert_eq!(r.domain().len(), 8);
    assert_eq!(r.required_zero(), Some([0, 1, 2, 3, 5].as_slice()));
    assert_eq!(r.observed_point(), Some(5));
    let mut first = vec![];
    let mut second = vec![];
    let mut whole = vec![];
    for (point, row) in r.columns()[0].rows().iter().enumerate() {
        let cs = row.components.as_ref().unwrap();
        assert_eq!(cs.len(), 2);
        assert_eq!(cs[0].path, vec![0]);
        assert_eq!(cs[0].ty, Type::Fp("2".into()));
        assert_eq!(cs[1].path, vec![1]);
        assert_eq!(cs[1].ty, Type::Bool);
        assert_eq!(cs[0].left, Some(fp(((point % 4) / 2) as u8)));
        assert_eq!(cs[0].right, Some(fp(0)));
        assert_eq!(cs[1].left, Some(Scalar::Bool(point % 2 == 1)));
        assert_eq!(cs[1].right, Some(Scalar::Bool(true)));
        first.push(cs[0].indicator.clone());
        second.push(cs[1].indicator.clone());
        whole.push(row.indicator.clone());
    }
    let ints = |v: &[u8]| v.iter().map(|&x| Some(BigInt::from(x))).collect::<Vec<_>>();
    assert_eq!(first, ints(&[0, 0, 0, 0, 0, 0, 1, 1]));
    assert_eq!(second, ints(&[0, 0, 0, 0, 1, 0, 1, 0]));
    assert_eq!(whole, ints(&[0, 0, 0, 0, 1, 0, 1, 1]));
    assert!(
        r.columns()[1]
            .rows()
            .iter()
            .all(|r| r.components.is_none() && r.indicator == Some(1.into()))
    );
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn nested_tuple_components_share_bool_fp2_fp3_without_mixing_characteristics() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required nested(c:Part):((c.quantity,c.third),c.flag)=((0,0),true);",
    );
    let r =
        finite_law_family_valuations(&i, &family_selection(&[("nested", bound())]), &mut quiet())
            .unwrap();
    assert!(r.is_complete());
    assert_eq!(r.domain().len(), 12);
    assert_eq!(r.observed_point(), None);
    assert_eq!(r.required_zero(), Some([6].as_slice()));
    assert_eq!(
        r.positions(),
        &[
            position("p", "flag"),
            position("p", "quantity"),
            position("p", "third")
        ]
    );
    for (values, row) in r.domain().iter().zip(r.columns()[0].rows()) {
        let cs = row.components.as_ref().unwrap();
        assert_eq!(cs.len(), 3);
        assert_eq!(
            cs.iter().map(|p| p.path.clone()).collect::<Vec<_>>(),
            vec![vec![0, 0], vec![0, 1], vec![1]]
        );
        assert_eq!(
            cs.iter().map(|p| p.ty.clone()).collect::<Vec<_>>(),
            vec![Type::Fp("2".into()), Type::Fp("3".into()), Type::Bool]
        );
        assert_eq!(cs[0].left.as_ref(), Some(&values[1]));
        assert_eq!(cs[1].left.as_ref(), Some(&values[2]));
        assert_eq!(cs[2].left.as_ref(), Some(&values[0]));
        let Scalar::Fp { value: q, .. } = &values[1] else {
            panic!()
        };
        let Scalar::Fp { value: t, .. } = &values[2] else {
            panic!()
        };
        let Scalar::Bool(flag) = values[0] else {
            panic!()
        };
        let expected = [q == &BigInt::from(0), t == &BigInt::from(0), flag];
        for (p, equal) in cs.iter().zip(expected) {
            assert_eq!(p.equal, Some(equal));
            assert_eq!(p.indicator, Some(BigInt::from(!equal as u8)));
        }
        assert_eq!(row.predicate, Some(expected.iter().all(|p| *p)));
    }
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn a_refuted_tuple_keeps_an_equal_component_zero_at_the_observed_point() {
    let i = fixture::with_body(fixture::MAP, "law required pair(c:Part):c.pair=(1,true);");
    let r = finite_law_valuations(&i, "Selected.pair", &bound(), &mut quiet()).unwrap();
    let row = &r.rows()[r.observed_point().unwrap()];
    assert_eq!(row.predicate, Some(false));
    assert_eq!(row.indicator, Some(1.into()));
    let cs = row.components.as_ref().unwrap();
    assert_eq!(cs[0].indicator, Some(1.into()));
    assert_eq!(cs[1].indicator, Some(0.into()));
    assert_eq!(cs[1].equal, Some(true));
    assert_eq!(cs[1].left, cs[1].right);
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn finite_term_components_use_extensional_equality_for_different_programs() {
    let i = fixture::with_body(
        fixture::MAP,
        "view left():Term<(Fp(2))->Fp(2)> =fn(n:Fp(2))=>n+0;view right():Term<(Fp(2))->Fp(2)> =fn(n:Fp(2))=>n;law required pair(a:Term<(Fp(2))->Fp(2)>,b:Term<(Fp(2))->Fp(2)>):(1,a)=(1,b);",
    );
    let a = literal_term(&i, "Selected.left");
    let b = literal_term(&i, "Selected.right");
    assert_ne!(a, b);
    let selected = family_selection(&[(
        "pair",
        vec![("a".into(), a.clone()), ("b".into(), b.clone())],
    )]);
    let r = finite_law_family_valuations(&i, &selected, &mut quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(r.domain(), &[Vec::<Scalar>::new()]);
    assert_eq!(r.required_zero(), Some([0].as_slice()));
    let row = &r.columns()[0].rows()[0];
    let cs = row.components.as_ref().unwrap();
    assert_eq!(cs[1].left.as_ref(), Some(&a));
    assert_eq!(cs[1].right.as_ref(), Some(&b));
    assert_eq!(cs[1].equal, Some(true));
    assert_eq!(cs[1].indicator, Some(0.into()));
    assert_eq!(row.predicate, Some(true));
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn finite_term_component_refutation_is_separate_from_an_equal_integer_component() {
    let i = fixture::with_body(
        fixture::MAP,
        "view left():Term<(Fp(2))->Fp(2)> =fn(n:Fp(2))=>n+1;view right():Term<(Fp(2))->Fp(2)> =fn(n:Fp(2))=>n;law required pair(a:Term<(Fp(2))->Fp(2)>,b:Term<(Fp(2))->Fp(2)>):(1,a)=(1,b);",
    );
    let r = finite_law_family_valuations(
        &i,
        &family_selection(&[(
            "pair",
            vec![
                ("a".into(), literal_term(&i, "Selected.left")),
                ("b".into(), literal_term(&i, "Selected.right")),
            ],
        )]),
        &mut quiet(),
    )
    .unwrap();
    assert!(r.is_complete());
    assert_eq!(r.required_zero(), Some([].as_slice()));
    let row = &r.columns()[0].rows()[0];
    let cs = row.components.as_ref().unwrap();
    assert_eq!(cs[0].equal, Some(true));
    assert_eq!(cs[0].indicator, Some(0.into()));
    assert_eq!(cs[1].equal, Some(false));
    assert_eq!(cs[1].indicator, Some(1.into()));
    assert_eq!(row.predicate, Some(false));
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn affine_term_components_keep_exact_equality_on_an_infinite_argument_domain() {
    let i = fixture::with_body(
        fixture::MAP,
        "view left():Term<(Z)->Z> =fn(n:Z)=>n+n;view right():Term<(Z)->Z> =fn(n:Z)=>2*n;law required pair(a:Term<(Z)->Z>,b:Term<(Z)->Z>):(unit,a)=(unit,b);",
    );
    let r = finite_law_family_valuations(
        &i,
        &family_selection(&[(
            "pair",
            vec![
                ("a".into(), literal_term(&i, "Selected.left")),
                ("b".into(), literal_term(&i, "Selected.right")),
            ],
        )]),
        &mut quiet(),
    )
    .unwrap();
    assert!(r.is_complete());
    assert_eq!(r.required_zero(), Some([0].as_slice()));
    let cs = r.columns()[0].rows()[0].components.as_ref().unwrap();
    assert_eq!(cs[0].ty, Type::Unit);
    assert_eq!(cs[0].left, Some(Scalar::Unit));
    assert_eq!(cs[0].equal, Some(true));
    assert_eq!(cs[1].equal, Some(true));
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn unsupported_term_component_preserves_the_known_whole_refutation() {
    let i = fixture::with_body(
        fixture::MAP,
        "view left():Term<(Z)->Z> =fn(n:Z)=>n*n;view right():Term<(Z)->Z> =fn(n:Z)=>n*n+0;law required pair(a:Term<(Z)->Z>,b:Term<(Z)->Z>):(0,a)=(1,b);",
    );
    let r = finite_law_family_valuations(
        &i,
        &family_selection(&[(
            "pair",
            vec![
                ("a".into(), literal_term(&i, "Selected.left")),
                ("b".into(), literal_term(&i, "Selected.right")),
            ],
        )]),
        &mut quiet(),
    )
    .unwrap();
    assert!(
        matches!(r.state(),FiniteLawState::Unavailable{location:Location::Law{..},feature} if feature=="元等式の成分外延比較に必要な算法")
    );
    assert!(r.domain_complete());
    assert!(!r.is_complete());
    assert_eq!(r.required_zero(), None);
    assert_eq!(r.domain(), &[Vec::<Scalar>::new()]);
    let row = &r.columns()[0].rows()[0];
    assert_eq!(row.predicate, Some(false));
    assert_eq!(row.indicator, Some(1.into()));
    let cs = row.components.as_ref().unwrap();
    assert_eq!(cs[0].equal, Some(false));
    assert_eq!(cs[0].indicator, Some(1.into()));
    assert!(cs[1].left.is_some() && cs[1].right.is_some());
    assert_eq!(cs[1].equal, None);
    assert_eq!(cs[1].indicator, None);
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn finite_ref_and_map_components_use_the_original_mathematical_values() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required ref(c:Part):c.link=c;law required table(c:Part):c.ownedtable=c.ownedtable;",
    );
    let r = finite_law_valuations(&i, "Selected.ref", &bound(), &mut quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(r.domain().len(), 2);
    for (point, row) in r.domain().iter().zip(r.rows()) {
        let p = &row.components.as_ref().unwrap()[0];
        assert!(p.path.is_empty());
        assert_eq!(p.ty, Type::Ref("Pattern.Part".into()));
        assert_eq!(p.equal, Some(point[0] == subject("p")));
    }
    let r = finite_law_valuations(&i, "Selected.table", &bound(), &mut quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(r.domain().len(), 10);
    for row in r.rows() {
        let p = &row.components.as_ref().unwrap()[0];
        assert!(matches!(p.ty, Type::Map(..)));
        assert_eq!(p.equal, Some(true));
        assert_eq!(p.indicator, Some(0.into()));
    }
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn non_equality_law_keeps_its_original_condition_and_has_no_fake_components() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required boolean(c:Part):c.flag and true;",
    );
    let r =
        finite_law_family_valuations(&i, &family_selection(&[("boolean", bound())]), &mut quiet())
            .unwrap();
    assert!(r.is_complete());
    assert_eq!(
        r.domain(),
        &[vec![Scalar::Bool(false)], vec![Scalar::Bool(true)]]
    );
    assert_eq!(r.required_zero(), Some([1].as_slice()));
    assert!(
        r.columns()[0]
            .rows()
            .iter()
            .all(|r| r.operands.is_none() && r.components.is_none())
    );
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn component_recheck_rejects_path_type_operands_equality_indicator_and_roster_forgery() {
    let i = fixture::with_body(fixture::MAP, "law required pair(c:Part):c.pair=(0,true);");
    let selected = family_selection(&[("pair", bound())]);
    for change in 0..12 {
        let mut r = finite_law_family_valuations(&i, &selected, &mut quiet()).unwrap();
        let row = &mut r.columns[0].rows[0];
        let cs = row.components.as_mut().unwrap();
        match change {
            0 => cs[0].path = vec![1],
            1 => cs[0].ty = Type::Bool,
            2 => cs[0].left = Some(fp(1)),
            3 => cs[0].right = Some(fp(1)),
            4 => cs[0].equal = Some(false),
            5 => cs[0].indicator = Some(1.into()),
            6 => cs.swap(0, 1),
            7 => {
                cs.pop();
            }
            8 => cs[0].equal = None,
            9 => row.components = None,
            10 => r.required_zero = Some(vec![]),
            _ => row.indicator = Some(0.into()),
        }
        assert!(r.recheck(&i, &mut quiet()).is_err(), "change={change}");
    }
}
#[test]
fn component_fixed_stops_keep_completed_rows_and_freeze_probe() {
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    let i = fixture::with_body(
        fixture::MAP,
        "law required pair(c:Part) when c.flag:c.pair=(0,true);",
    );
    let selected = family_selection(&[("pair", bound())]);
    let run = |at: usize, signal: Signal| {
        let seen = Rc::new(Cell::new(0));
        let visits = seen.clone();
        let calls = Rc::new(Cell::new(0));
        let sampled = calls.clone();
        (
            Control::new(move |p| {
                sampled.set(sampled.get() + 1);
                if p == Checkpoint::FiniteLawComponent {
                    visits.set(visits.get() + 1);
                }
                (visits.get() >= at).then_some(signal)
            }),
            seen,
            calls,
        )
    };
    let (mut c, total, _) = run(usize::MAX, Signal::Int);
    finite_law_family_valuations(&i, &selected, &mut c).unwrap();
    let total = total.get();
    assert!(total > 3);
    for at in [1, total / 2, total] {
        for signal in [Signal::Int, Signal::Term] {
            let (mut c, _, calls) = run(at, signal);
            let failure = match finite_law_family_valuations(&i, &selected, &mut c) {
                Err(f) => f,
                Ok(_) => panic!("停止が成功"),
            };
            assert!(matches!(failure.cause,ValidationFailure::Stop(ref s) if s==&signal));
            let partial = failure.partial.unwrap();
            assert!(!partial.is_complete());
            assert_eq!(partial.required_zero(), None);
            for q in partial.columns() {
                for (p, row) in q.rows().iter().enumerate() {
                    assert_eq!(row.point, p);
                    assert!(
                        row.components
                            .as_ref()
                            .unwrap()
                            .iter()
                            .all(|p| p.indicator.is_some())
                    );
                }
            }
            let before = calls.get();
            assert_eq!(c.checkpoint(Checkpoint::FiniteLawComponent), Err(signal));
            assert_eq!(before, calls.get());
        }
    }
}
