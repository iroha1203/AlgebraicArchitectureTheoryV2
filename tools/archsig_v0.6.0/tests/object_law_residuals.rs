use archsig::{
    canonical::Json,
    construction::readings::{
        LawNumericShape, LawResidualOutcome as Outcome, ObjectLawResiduals,
        ObjectLawResidualsFailure, object_law_residuals,
    },
    observed::{
        control::{Control, Limits, Usage},
        input::{CheckedInputs, InputSources, check_inputs},
    },
    types::Type,
};
use std::sync::Arc;
#[path = "common/object_view_compatibility_data.rs"]
mod fixture;
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn inputs(body: &str, map: &str) -> Arc<CheckedInputs> {
    inputs_with_definitions(fixture::D, body, map)
}
fn inputs_with_definitions(definitions: &str, body: &str, map: &str) -> Arc<CheckedInputs> {
    let d =
        archsig::definition::check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &d.vocabularies["Pattern"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Selected {{ use vocabulary Pattern version \"1\" digest \"{digest}\"; {body} }}"
    );
    Arc::new(
        check_inputs(
            InputSources::from_bytes(
                vec![definitions.as_bytes().to_vec()],
                law.into_bytes(),
                map.replace("@DIGEST@", digest).into_bytes(),
            ),
            &mut quiet(),
        )
        .unwrap_or_else(|f| panic!("{:?}", f.issues())),
    )
}
fn run(i: Arc<CheckedInputs>) -> ObjectLawResiduals {
    object_law_residuals(i, "Selected", "v", "root", &mut quiet())
        .unwrap_or_else(|f| panic!("{f:?}"))
}
fn missing() -> String {
    fixture::A
        .lines()
        .filter(|l| !l.contains("\"quantity-p\""))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]")
}
fn text(v: &Option<archsig::construction::maps::NumericTransportValue>) -> Option<String> {
    v.as_ref().map(|v| v.wire().canonical())
}
#[test]
fn two_false_laws_have_distinct_original_numeric_residuals_with_a_zero_tuple_component() {
    let i = inputs(
        "law required amount(c:Part):((if (forall a:Root . false) then 2 else 3),c.quantity)=(0,2);",
        fixture::A,
    );
    let r = run(Arc::clone(&i));
    assert!(r.is_complete());
    assert_eq!(r.evaluations().len(), 2);
    assert_eq!(
        r.base().outcome(),
        Some(&archsig::construction::readings::LawCompatibilityOutcome::Compatible)
    );
    assert_eq!(r.outcome(), Some(&Outcome::Refuted { component: vec![0] }));
    for (e, expected) in r.evaluations().iter().zip(["3", "2"]) {
        assert!(e.complete);
        assert!(matches!(
            e.shape,
            LawNumericShape::Equality {
                ty: Type::Tuple(_),
                ..
            }
        ));
        let case = &e.rows[0].cases[0];
        assert!(case.complete);
        assert_eq!(case.reading.body(), Some(false));
        assert_eq!(case.components.len(), 2);
        assert_eq!(case.components[0].path, vec![0]);
        assert_eq!(case.components[1].path, vec![1]);
        assert_eq!(
            text(&case.components[0].left),
            Some(format!("\"{expected}\""))
        );
        assert_eq!(text(&case.components[0].right), Some("\"0\"".into()));
        assert_eq!(
            text(&case.components[0].epsilon),
            Some(format!("\"{expected}\""))
        );
        assert_eq!(case.components[0].epsilon, case.components[0].residual);
        assert_eq!(text(&case.components[1].epsilon), Some("\"0\"".into()));
        assert!(case.epsilon_producer.is_some());
        assert_eq!(case.operand_evaluations.len(), 2);
    }
    assert_eq!(
        r.comparisons()[0].points[0].components,
        [Outcome::Refuted { component: vec![0] }, Outcome::Compatible]
    );
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn all_boolean_arguments_and_q_fp_components_keep_the_original_rings_and_values() {
    let i = inputs(
        "view half():Q=rat(1,2); view third():Q=rat(1,3); view field():Fp(5)=3; law optional family(c:Part,b:Bool):((if b then 5 else 2),(half(),field()))=(2,(third(),1));",
        fixture::A,
    );
    let r = run(Arc::clone(&i));
    assert_eq!(r.outcome(), Some(&Outcome::Compatible));
    assert_eq!(r.comparisons()[0].points.len(), 2);
    for e in r.evaluations() {
        assert_eq!(e.rows.len(), 2);
        for (j, row) in e.rows.iter().enumerate() {
            let c = &row.cases[0];
            assert!(!c.reading.required());
            assert_eq!(c.components.len(), 3);
            assert_eq!(c.components[0].ty, Type::Z);
            assert_eq!(c.components[1].ty, Type::Q);
            assert_eq!(c.components[2].ty, Type::Fp("5".into()));
            assert_eq!(c.components[1].path, vec![1, 0]);
            assert_eq!(c.components[2].path, vec![1, 1]);
            assert_eq!(
                text(&c.components[0].epsilon),
                Some(if j == 0 { "\"0\"" } else { "\"3\"" }.into())
            );
            assert_eq!(text(&c.components[1].epsilon), Some("[\"1\",\"6\"]".into()));
            assert_eq!(text(&c.components[2].epsilon), Some("\"2\"".into()));
        }
    }
    for (p, b) in r.comparisons()[0].points.iter().zip([false, true]) {
        assert_eq!(p.arguments[0].wire(), Json::Bool(b));
    }
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn guard_false_keeps_raw_difference_separate_from_zero_conditioned_residual() {
    let i = inputs(
        "law required guarded(c:Part) when false:c.quantity=0;",
        fixture::A,
    );
    let r = run(Arc::clone(&i));
    assert_eq!(r.outcome(), Some(&Outcome::Compatible));
    for e in r.evaluations() {
        let c = &e.rows[0].cases[0];
        assert_eq!(c.reading.application().value(), Some(false));
        assert_eq!(text(&c.components[0].residual), Some("\"0\"".into()));
        if c.epsilon_producer.is_some() {
            assert_eq!(text(&c.components[0].epsilon), Some("\"2\"".into()));
        }
    }
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn outside_object_uses_typed_zero_without_inventing_raw_operands_or_fake_parameters() {
    let i = inputs("law required rootOnly(a:Root,b:Bool):2=1;", fixture::A);
    let r = run(Arc::clone(&i));
    let outside = r
        .evaluations()
        .iter()
        .find(|e| e.uniform.is_some())
        .unwrap();
    let row = outside.uniform.as_ref().unwrap();
    assert!(outside.rows.is_empty());
    let c = &row.cases[0];
    assert_eq!(c.reading.application().value(), Some(false));
    assert!(c.evaluation.is_none());
    assert!(c.components[0].epsilon.is_none());
    assert!(c.components[0].left.is_none());
    assert_eq!(text(&c.components[0].residual), Some("\"0\"".into()));
    assert_eq!(r.comparisons()[0].points.len(), 2);
    assert_eq!(r.outcome(), Some(&Outcome::Refuted { component: vec![] }));
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn unread_operands_and_affine_identity_are_not_replaced_by_zero_raw_difference() {
    for law in ["c.quantity=2", "c.quantity=c.quantity"] {
        let i = inputs(&format!("law required missing(c:Part):{law};"), &missing());
        let r = run(Arc::clone(&i));
        assert_eq!(r.outcome(), Some(&Outcome::Undetermined));
        for e in r.evaluations() {
            let c = &e.rows[0].cases[0];
            assert!(c.components[0].left.is_none());
            assert!(c.components[0].epsilon.is_none());
            assert!(c.components[0].residual.is_none());
        }
        r.recheck(i, &mut quiet()).unwrap();
    }
}
#[test]
fn unsupported_numeric_realization_keeps_the_original_condition() {
    let i = inputs("law optional condition(c:Part):c.quantity>0;", fixture::A);
    let r = run(Arc::clone(&i));
    assert_eq!(r.outcome(), Some(&Outcome::Unsupported));
    for e in r.evaluations() {
        assert!(matches!(
            e.shape,
            LawNumericShape::Unsupported { ty: Type::Bool, .. }
        ));
        assert_eq!(e.rows[0].cases[0].reading.body(), Some(true));
        assert!(e.rows[0].cases[0].components.is_empty());
    }
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn a_grouped_equality_preserves_original_operands_and_epsilon() {
    let i = inputs("law required grouped(c:Part):((c.quantity=1));", fixture::A);
    let r = run(Arc::clone(&i));
    assert_eq!(r.outcome(), Some(&Outcome::Compatible));
    for e in r.evaluations() {
        assert_eq!(
            text(&e.rows[0].cases[0].components[0].epsilon),
            Some("\"1\"".into())
        );
    }
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn recheck_rejects_changed_current_inputs_and_retains_the_recomputed_result() {
    let i = inputs("law required amount(c:Part):c.quantity=2;", fixture::A);
    let r = run(i);
    let changed = inputs("law required amount(c:Part):c.quantity=3;", fixture::A);
    assert!(matches!(
        r.recheck(changed, &mut quiet()),
        Err(ObjectLawResidualsFailure::Original(_))
    ));
}
#[test]
fn ground_and_finite_rows_keep_all_missing_boolean_completion_cases() {
    let d = fixture::D.replace("\"type\":\"Z\"", "\"type\":\"Bool\"");
    for parameter in ["", ",b:Bool"] {
        let i = inputs_with_definitions(
            &d,
            &format!("law required cases(c:Part{parameter}):(if c.quantity then 1 else 2)=0;"),
            &missing(),
        );
        let r = run(Arc::clone(&i));
        assert_eq!(r.outcome(), Some(&Outcome::Undetermined));
        for e in r.evaluations() {
            assert_eq!(e.rows.len(), if parameter.is_empty() { 1 } else { 2 });
            for row in &e.rows {
                assert!(row.complete);
                assert_eq!(row.cases.len(), 2);
                let values = row
                    .cases
                    .iter()
                    .map(|c| {
                        assert!(c.complete);
                        assert_eq!(c.reading.application().value(), Some(true));
                        text(&c.components[0].epsilon).unwrap()
                    })
                    .collect::<Vec<_>>();
                assert_eq!(values, ["\"2\"", "\"1\""]);
                assert_ne!(row.cases[0].evaluation, row.cases[1].evaluation);
            }
        }
        r.recheck(i, &mut quiet()).unwrap();
    }
}
#[test]
fn unknown_guards_keep_both_applicable_and_inapplicable_cases_undetermined() {
    let d = fixture::D.replace("\"type\":\"Z\"", "\"type\":\"Bool\"");
    for body in ["2=1", "2=2"] {
        let i = inputs_with_definitions(
            &d,
            &format!("law required guarded(c:Part,b:Bool) when c.quantity:{body};"),
            &missing(),
        );
        let r = run(Arc::clone(&i));
        assert_eq!(r.outcome(), Some(&Outcome::Undetermined));
        for e in r.evaluations() {
            for row in &e.rows {
                assert_eq!(row.cases.len(), 2);
                assert_eq!(row.cases[0].reading.application().value(), Some(false));
                assert_eq!(row.cases[1].reading.application().value(), Some(true));
                assert_eq!(
                    text(&row.cases[0].components[0].residual),
                    Some("\"0\"".into())
                );
            }
        }
        r.recheck(i, &mut quiet()).unwrap();
    }
}
#[test]
fn a_guarded_unsupported_body_keeps_its_original_false_body_and_true_conditional() {
    let i = inputs(
        "law optional unsupported(c:Part) when false:false;",
        fixture::A,
    );
    let r = run(Arc::clone(&i));
    assert_eq!(r.outcome(), Some(&Outcome::Unsupported));
    for e in r.evaluations() {
        let c = &e.rows[0].cases[0];
        assert_eq!(c.reading.application().value(), Some(false));
        assert_eq!(c.reading.body(), Some(false));
        assert_eq!(c.reading.conditional(), Some(true));
    }
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn a_finite_false_guard_keeps_unread_original_body_and_zero_conditioned_residual() {
    let i = inputs(
        "law required guarded(c:Part,b:Bool) when false:c.quantity=0;",
        &missing(),
    );
    let r = run(Arc::clone(&i));
    assert_eq!(r.outcome(), Some(&Outcome::Compatible));
    for e in r.evaluations() {
        assert_eq!(e.rows.len(), 2);
        for row in &e.rows {
            let c = &row.cases[0];
            assert!(c.body_evaluation.is_none());
            assert!(c.operand_values.is_empty());
            assert!(c.components[0].epsilon.is_none());
            assert!(c.components[0].left.is_none());
            assert_eq!(text(&c.components[0].residual), Some("\"0\"".into()));
        }
    }
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn empty_actual_parameter_domains_are_not_fabricated_as_a_zero_argument_row() {
    let i = inputs(
        "law required empty(c:Part,x:(Vacant,Bool)):2=1;",
        fixture::A,
    );
    let r = run(Arc::clone(&i));
    assert_eq!(r.outcome(), Some(&Outcome::Compatible));
    for e in r.evaluations() {
        assert!(e.complete);
        assert!(e.rows.is_empty());
        assert!(e.uniform.is_none());
    }
    assert!(r.comparisons()[0].points.is_empty());
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn unbounded_identity_law_preserves_symbolic_zero_residuals() {
    let i = inputs("law required unbounded(c:Part,z:Z):z=z;", fixture::A);
    let r = run(Arc::clone(&i));
    assert!(r.is_complete());
    assert_eq!(r.outcome(), Some(&Outcome::Compatible));
    assert_eq!(r.evaluations().len(), 2);
    for e in r.evaluations() {
        assert!(e.complete);
        assert!(e.rows.is_empty());
        let row = e.uniform.as_ref().unwrap();
        assert!(row.complete);
        assert_eq!(row.cases.len(), 1);
        assert_eq!(row.cases[0].reading.body(), Some(true));
        assert_eq!(row.cases[0].components.len(), 1);
        assert_eq!(text(&row.cases[0].components[0].epsilon), Some("\"0\"".into()));
        assert_eq!(row.cases[0].components[0].epsilon, row.cases[0].components[0].residual);
    }
    r.recheck(i, &mut quiet()).unwrap();
}

#[test]
fn different_complete_patterns_keep_their_own_numeric_laws_without_equality_obligations() {
    let map=fixture::A.replace("{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}","{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"},{\"id\":\"r\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}")
        .replace("\"atoms\":[","\"atoms\":[{\"id\":\"owner-r\",\"subject\":\"r\",\"field\":\"Pattern.Part.owner\",\"value\":[\"v\",\"root\"],\"origin\":\"model\"},{\"id\":\"quantity-r\",\"subject\":\"r\",\"field\":\"Pattern.Part.quantity\",\"value\":\"5\",\"origin\":\"model\"},");
    let i = inputs("law required amount(c:Part):c.quantity=2;", &map);
    let r = run(Arc::clone(&i));
    assert_eq!(r.base().profiles().classes().unwrap().len(), 3);
    assert!(r.comparisons().is_empty());
    assert_eq!(r.evaluations().len(), 6);
    assert_eq!(r.outcome(), Some(&Outcome::Compatible));
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn fixed_stops_keep_original_execution_completed_cases_refutations_and_final_completion() {
    use archsig::{observed::control::Checkpoint as C, result::Signal};
    use std::{cell::RefCell, rc::Rc};
    let i = inputs(
        "law required amount(c:Part,b:Bool):((if (forall a:Root . false) then 2 else 3),c.quantity)=(0,2);",
        fixture::A,
    );
    let history = Rc::new(RefCell::new(Vec::new()));
    let h = history.clone();
    let mut traced = Control::new(Limits::default(), move |p| {
        h.borrow_mut().push(p);
        Usage::default()
    });
    object_law_residuals(i.clone(), "Selected", "v", "root", &mut traced).unwrap();
    for point in [
        C::Expression,
        C::ObjectLawResiduals,
        C::ObjectLawResidualCase,
        C::ObjectLawResidualPoint,
    ] {
        let count = history.borrow().iter().filter(|p| **p == point).count();
        assert!(count > 0);
        let mut targets = vec![1, count];
        if count > 2 {
            targets.push(count / 2)
        }
        targets.sort();
        targets.dedup();
        for nth in targets {
            for mode in 0..4 {
                let hits = Rc::new(RefCell::new(0));
                let hits0 = hits.clone();
                let probes = Rc::new(RefCell::new(0));
                let probes0 = probes.clone();
                let limits = Limits {
                    time_ms: (mode == 0).then_some(1),
                    memory_mib: (mode == 1).then_some(1),
                };
                let mut c = Control::new(limits, move |p| {
                    *probes0.borrow_mut() += 1;
                    if p == point {
                        *hits0.borrow_mut() += 1;
                    }
                    if p == point && *hits0.borrow() == nth {
                        Usage {
                            elapsed_ms: if mode == 0 { 1 } else { 0 },
                            memory_mib: if mode == 1 { 1 } else { 0 },
                            signal: match mode {
                                2 => Some(Signal::Int),
                                3 => Some(Signal::Term),
                                _ => None,
                            },
                        }
                    } else {
                        Usage::default()
                    }
                });
                let f =
                    object_law_residuals(i.clone(), "Selected", "v", "root", &mut c).unwrap_err();
                assert!(c.stop_reason().is_some());
                match f {
                    ObjectLawResidualsFailure::Original(f) => {
                        assert_eq!(point, C::Expression);
                        assert!(f.partial().is_some());
                    }
                    ObjectLawResidualsFailure::Reading { partial, .. } => {
                        assert!(partial.base().is_complete());
                        if point == C::ObjectLawResidualCase {
                            assert!(
                                partial
                                    .evaluations()
                                    .iter()
                                    .flat_map(|e| &e.rows)
                                    .flat_map(|r| &r.cases)
                                    .any(|c| c.complete)
                            );
                        }
                        if point == C::ObjectLawResidualPoint {
                            assert_eq!(
                                partial.outcome(),
                                Some(&Outcome::Refuted { component: vec![0] })
                            );
                            if nth == count {
                                assert!(partial.is_complete());
                                assert!(partial.comparisons().iter().all(|v| v.outcome.is_some()));
                            }
                        }
                        if point == C::ObjectLawResiduals && nth == count {
                            assert!(partial.is_complete());
                        }
                    }
                }
                let before = *probes.borrow();
                assert!(c.checkpoint(C::Resolve).is_err());
                assert_eq!(*probes.borrow(), before);
            }
        }
    }
}
#[test]
fn recheck_stops_keep_the_completed_recomputed_numeric_result_and_freeze_probes() {
    use archsig::observed::control::Checkpoint as C;
    use std::{cell::RefCell, rc::Rc};
    let i = inputs("law required amount(c:Part):c.quantity=2;", fixture::A);
    let r = run(i.clone());
    let count = Rc::new(RefCell::new(0));
    let count0 = count.clone();
    let mut trace = Control::new(Limits::default(), move |p| {
        if p == C::ObjectLawResiduals {
            *count0.borrow_mut() += 1
        }
        Usage::default()
    });
    r.recheck(i.clone(), &mut trace).unwrap();
    let nth = *count.borrow();
    assert!(nth > 0);
    use archsig::{
        construction::ConstructionFailure,
        observed::control::{Resource, StopReason},
        result::Signal,
    };
    for mode in 0..4 {
        let calls = Rc::new(RefCell::new(0));
        let calls0 = calls.clone();
        let probes = Rc::new(RefCell::new(0));
        let probes0 = probes.clone();
        let mut c = Control::new(
            Limits {
                time_ms: (mode == 0).then_some(1),
                memory_mib: (mode == 1).then_some(1),
            },
            move |p| {
                *probes0.borrow_mut() += 1;
                if p == C::ObjectLawResiduals {
                    *calls0.borrow_mut() += 1
                }
                if *calls0.borrow() != nth {
                    return Usage::default();
                }
                Usage {
                    elapsed_ms: if mode == 0 { 1 } else { 0 },
                    memory_mib: if mode == 1 { 1 } else { 0 },
                    signal: match mode {
                        2 => Some(Signal::Int),
                        3 => Some(Signal::Term),
                        _ => None,
                    },
                }
            },
        );
        let expected = match mode {
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
        let failure = r.recheck(i.clone(), &mut c).unwrap_err();
        let ObjectLawResidualsFailure::Reading {
            cause: ConstructionFailure::Stopped(reason),
            partial,
        } = failure
        else {
            panic!("recheck must retain the completed numeric result: mode={mode}");
        };
        assert_eq!(reason, expected);
        assert_eq!(c.stop_reason(), Some(expected));
        assert!(partial.is_complete());
        assert_eq!(partial.outcome(), Some(&Outcome::Compatible));
        assert!(partial.evaluations().iter().all(|e| e.complete));
        let n = *calls.borrow();
        let observed = *probes.borrow();
        assert_eq!(n, nth);
        assert!(c.checkpoint(C::ObjectLawResiduals).is_err());
        assert!(c.checkpoint(C::Expression).is_err());
        assert_eq!(n, *calls.borrow());
        assert_eq!(observed, *probes.borrow());
    }
}
#[test]
fn each_actual_fp_argument_keeps_its_own_scalar_residual_without_changing_the_integer_ring() {
    let i = inputs(
        "law required field(c:Part,n:Fp(5)):(n,2)=(0,1);",
        fixture::A,
    );
    let r = run(Arc::clone(&i));
    assert_eq!(r.outcome(), Some(&Outcome::Compatible));
    assert_eq!(r.comparisons()[0].points.len(), 5);
    for e in r.evaluations() {
        assert_eq!(e.rows.len(), 5);
        for (n, row) in e.rows.iter().enumerate() {
            let c = &row.cases[0];
            assert_eq!(c.components[0].ty, Type::Fp("5".into()));
            assert_eq!(c.components[1].ty, Type::Z);
            assert_eq!(text(&c.components[0].epsilon), Some(format!("\"{n}\"")));
            assert_eq!(text(&c.components[1].epsilon), Some("\"1\"".into()));
        }
    }
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn every_original_instance_in_a_shared_pattern_is_compared_at_every_actual_argument() {
    let i = inputs(
        "law required amount(c:Part,b:Bool):(if (forall a:Root . false) then 2 else 3)=0; law optional other(c:Part,n:Fp(3)):n=0; law required ground(c:Part):c.quantity=2;",
        fixture::A,
    );
    let r = run(Arc::clone(&i));
    assert_eq!(r.base().profiles().classes().unwrap(), [vec![0, 1]]);
    assert_eq!(r.evaluations().len(), 6);
    assert_eq!(r.comparisons().len(), 3);
    let mut instances = std::collections::BTreeSet::new();
    for p in r.comparisons() {
        assert_eq!((p.source_object, p.target_object), (0, 1));
        assert!(instances.insert(p.instance));
        let name = &r.base().readings().instances()[p.instance]
            .declaration()
            .name;
        match name.as_str() {
            "Selected.amount" => {
                assert_eq!(p.points.len(), 2);
                assert_eq!(p.outcome, Some(Outcome::Refuted { component: vec![] }));
            }
            "Selected.other" => {
                assert_eq!(p.points.len(), 3);
                assert_eq!(p.outcome, Some(Outcome::Compatible));
            }
            "Selected.ground" => {
                assert_eq!(p.points.len(), 1);
                assert_eq!(p.outcome, Some(Outcome::Compatible));
            }
            _ => panic!("unexpected original instance {name}"),
        }
    }
    r.recheck(i, &mut quiet()).unwrap();
}

#[test]
fn conditional_membership_keeps_unknown_residuals_and_the_original_owner_condition() {
    let map=fixture::A.replace("{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}","{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"},{\"id\":\"t\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}");
    let i = inputs("law required amount(c:Part,b:Bool):c.quantity=0;", &map);
    let r = run(Arc::clone(&i));
    assert_eq!(r.outcome(), Some(&Outcome::Undetermined));
    let mut count = 0;
    for e in r.evaluations() {
        if let Some(row) = &e.uniform {
            let c = &row.cases[0];
            if matches!(
                c.reading.application(),
                archsig::construction::maps::LawApplication::ConditionalMembership(_)
            ) {
                count += 1;
                assert!(c.components[0].epsilon.is_none());
                assert!(c.components[0].residual.is_none());
            }
        }
    }
    assert!(count > 0);
    r.recheck(i, &mut quiet()).unwrap();
}

#[test]
fn conjunction_keeps_distinct_signed_residuals_and_original_operand_pairs() {
    let i = inputs("law required both(c:Part):(c.quantity=0) and (c.quantity=3);", fixture::A);
    let r = run(i.clone());
    assert!(r.is_complete());
    for e in r.evaluations() {
        assert!(matches!(e.shape, LawNumericShape::Conjunction { .. }));
        let case = &e.rows[0].cases[0];
        assert_eq!(case.reading.body(), Some(false));
        assert_eq!(case.components.len(), 2);
        assert_eq!(case.components[0].path, [0]);
        assert_eq!(case.components[1].path, [1]);
        assert_eq!(text(&case.components[0].epsilon), Some("\"2\"".into()));
        assert_eq!(text(&case.components[1].epsilon), Some("\"-1\"".into()));
        assert_eq!(case.conjuncts.len(), 2);
        for term in &case.conjuncts {
            assert_eq!(term.operand_evaluations.len(), 2);
            assert!(term.epsilon_producer.is_some());
        }
        assert_ne!(case.conjuncts[0].operand_evaluations, case.conjuncts[1].operand_evaluations);
    }
    r.recheck(i, &mut quiet()).unwrap();
}
