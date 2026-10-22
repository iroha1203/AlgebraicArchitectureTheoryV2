use super::*;
use crate::observed::control::{Control, Limits, Usage};
#[allow(dead_code)]
mod fixture {
    include!("../../tests/common/primitive_valuation_data.rs");
}
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn subject(name: &str) -> Scalar {
    Scalar::Subject {
        snapshot: "v".into(),
        subject: name.into(),
        entity: if name == "p" || name == "q" {
            "Pattern.Part"
        } else {
            "Pattern.Root"
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
fn unsupported_candidate_path_does_not_reuse_observed_action_as_a_completed_table() {
    mod paths {
        use crate as archsig;
        include!("../../tests/common/internal_paths.rs");
    }
    use crate::observed::input::{InputSources, check_inputs};
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
    assert!(
        matches!(r.state(),FiniteLawState::Unavailable{location:Location::Law{..},feature} if feature=="原始候補に対するPath作用の構成")
    );
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
    use crate::{
        observed::control::{Resource, StopReason},
        result::Signal,
    };
    use std::{cell::Cell, rc::Rc};
    fn control(
        point: Checkpoint,
        at: usize,
        kind: u8,
    ) -> (Control, Rc<Cell<usize>>, Rc<Cell<usize>>) {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let calls = Rc::new(Cell::new(0));
        let sampled = calls.clone();
        (
            Control::new(
                Limits {
                    time_ms: Some(1),
                    memory_mib: Some(1),
                },
                move |p| {
                    sampled.set(sampled.get() + 1);
                    if p == point {
                        seen.set(seen.get() + 1)
                    }
                    let stop = seen.get() >= at;
                    Usage {
                        elapsed_ms: if stop && kind == 0 { 1 } else { 0 },
                        memory_mib: if stop && kind == 1 { 1 } else { 0 },
                        signal: if stop {
                            match kind {
                                2 => Some(Signal::Int),
                                3 => Some(Signal::Term),
                                _ => None,
                            }
                        } else {
                            None
                        },
                    }
                },
            ),
            count,
            calls,
        )
    }
    let i = fixture::inputs();
    for point in [Checkpoint::FiniteLawDomain, Checkpoint::FiniteLawEvaluation] {
        let (mut c, count, _) = control(point, usize::MAX, 4);
        finite_law_valuations(&i, "Selected.guarded", &bound(), &mut c).unwrap();
        let total = count.get();
        assert!(total > 1);
        for at in [1, total] {
            for kind in 0..4 {
                let (mut c, _, calls) = control(point, at, kind);
                let failure = match finite_law_valuations(&i, "Selected.guarded", &bound(), &mut c)
                {
                    Err(f) => f,
                    Ok(_) => panic!("停止が成功になった"),
                };
                let expected = match kind {
                    0 => StopReason::BudgetExhausted {
                        resource: Resource::TimeMs,
                        limit: 1,
                        observed: 1,
                    },
                    1 => StopReason::BudgetExhausted {
                        resource: Resource::MemoryMib,
                        limit: 1,
                        observed: 1,
                    },
                    2 => StopReason::Cancelled(Signal::Int),
                    _ => StopReason::Cancelled(Signal::Term),
                };
                assert!(matches!(failure.cause,ValidationFailure::Stop(ref s) if s==&expected));
                let partial = failure.partial.unwrap();
                assert!(!partial.is_complete());
                // 完成フラグに到達しても、停止した実行全体を成功結果として返さない。
                if !partial.domain_complete() {
                    assert!(partial.rows().is_empty());
                }
                assert!(partial.rows().iter().all(|r| r.indicator.is_some()));
                let before = calls.get();
                assert_eq!(c.checkpoint(point), Err(expected));
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
    use crate::observed::input::{InputSources, check_inputs};
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
    use crate::{
        observed::control::{Resource, StopReason},
        result::Signal,
    };
    use std::{cell::Cell, rc::Rc};
    fn controlled(at: usize, kind: u8) -> (Control, Rc<Cell<usize>>, Rc<Cell<usize>>) {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let calls = Rc::new(Cell::new(0));
        let all = calls.clone();
        (
            Control::new(
                Limits {
                    time_ms: Some(1),
                    memory_mib: Some(1),
                },
                move |point| {
                    all.set(all.get() + 1);
                    if point == Checkpoint::ArchMapTerm {
                        seen.set(seen.get() + 1);
                    }
                    let stop = seen.get() >= at;
                    Usage {
                        elapsed_ms: if stop && kind == 0 { 1 } else { 0 },
                        memory_mib: if stop && kind == 1 { 1 } else { 0 },
                        signal: if stop {
                            match kind {
                                2 => Some(Signal::Int),
                                3 => Some(Signal::Term),
                                _ => None,
                            }
                        } else {
                            None
                        },
                    }
                },
            ),
            count,
            calls,
        )
    }
    let i = fixture::with_body(
        fixture::MAP,
        "view make():Term<(Fp(2))->Fp(2)> =fn(n:Fp(2))=>n+1;law required fixed(t:Term<(Fp(2))->Fp(2)>):t(0)=1;",
    );
    let bindings = vec![("t".into(), literal_term(&i, "Selected.make"))];
    let (mut c, count, _) = controlled(usize::MAX, 4);
    assert!(
        finite_law_valuations(&i, "Selected.fixed", &bindings, &mut c)
            .unwrap()
            .is_complete()
    );
    let total = count.get();
    assert!(total > 1);
    for at in [1, total] {
        for kind in 0..4 {
            let (mut c, _, calls) = controlled(at, kind);
            let failure = match finite_law_valuations(&i, "Selected.fixed", &bindings, &mut c) {
                Err(f) => f,
                Ok(_) => panic!("中断後に完成表を返した"),
            };
            let expected = match kind {
                0 => StopReason::BudgetExhausted {
                    resource: Resource::TimeMs,
                    limit: 1,
                    observed: 1,
                },
                1 => StopReason::BudgetExhausted {
                    resource: Resource::MemoryMib,
                    limit: 1,
                    observed: 1,
                },
                2 => StopReason::Cancelled(Signal::Int),
                _ => StopReason::Cancelled(Signal::Term),
            };
            assert!(matches!(failure.cause,ValidationFailure::Stop(ref s) if s==&expected));
            let partial = failure.partial.unwrap();
            assert!(!partial.is_complete());
            assert!(partial.rows().is_empty());
            let before = calls.get();
            assert_eq!(c.checkpoint(Checkpoint::ArchMapTerm), Err(expected));
            assert_eq!(calls.get(), before);
        }
    }
}

#[test]
fn registered_identity_and_reconstructed_path_bindings_are_accepted_but_forged_actions_are_not() {
    mod paths {
        use crate as archsig;
        include!("../../tests/common/internal_paths.rs");
    }
    use crate::observed::input::{InputSources, check_inputs};
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
