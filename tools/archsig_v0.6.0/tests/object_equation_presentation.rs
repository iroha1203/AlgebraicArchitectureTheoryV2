use archsig::{
    construction::readings::{
        EquationGuard as G, EquationPolynomial, EquationPresentation, EquationPresentationFailure,
        EquationPresentationStatus as S, object_equation_presentation,
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
fn inputs_with(definition: &str, body: &str, map: &str) -> Arc<CheckedInputs> {
    let d =
        archsig::definition::check_definitions(&[("definition0", definition.as_bytes())]).unwrap();
    let digest = &d.vocabularies["Pattern"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Selected {{use vocabulary Pattern version \"1\" digest \"{digest}\"; {body}}}"
    );
    Arc::new(
        check_inputs(
            InputSources::from_bytes(
                vec![definition.as_bytes().to_vec()],
                law.into_bytes(),
                map.replace("@DIGEST@", digest).into_bytes(),
            ),
            &mut quiet(),
        )
        .unwrap_or_else(|f| panic!("{:?}", f.issues())),
    )
}
fn inputs(body: &str) -> Arc<CheckedInputs> {
    inputs_with(fixture::D, body, fixture::A)
}
fn run(i: Arc<CheckedInputs>) -> EquationPresentation {
    object_equation_presentation(i, "Selected", "v", "root", 0, &mut quiet())
        .unwrap_or_else(|f| panic!("{f:?}"))
}
fn terms(p: &EquationPolynomial) -> Vec<(Vec<usize>, String)> {
    p.terms
        .iter()
        .map(|t| (t.variables.clone(), t.coefficient.wire().canonical()))
        .collect()
}
fn number(v: &Option<archsig::construction::maps::NumericTransportValue>) -> Option<String> {
    v.as_ref().map(|v| v.wire().canonical())
}
#[test]
fn required_equations_share_x_and_keep_x_and_x_minus_one_without_quotienting() {
    let i = inputs(
        "law required zero(c:Part):c.quantity=0;law required one(c:Part):c.quantity=1;law optional two(c:Part):c.quantity=2;",
    );
    let r = run(i.clone());
    assert!(r.is_complete());
    assert_eq!(r.status(), S::Ready);
    assert_eq!(r.rings().len(), 1);
    let ring = &r.rings()[0];
    assert_eq!(ring.ty, Type::Z);
    assert_eq!(ring.symbols.len(), 1);
    assert_eq!(ring.symbols[0].slot.subject, "p");
    assert_eq!(ring.symbols[0].slot.field, "Pattern.Part.quantity");
    assert_eq!(ring.symbols[0].readings.len(), 3);
    assert_eq!(
        terms(&ring.evaluation_images.as_ref().unwrap()[0]),
        [(vec![], "\"2\"".into())]
    );
    assert_eq!(number(&ring.symbols[0].value), Some("\"2\"".into()));
    let names: Vec<_> = r
        .occurrences()
        .iter()
        .map(|q| {
            r.base().base().readings().instances()[q.position.instance]
                .declaration()
                .name
                .as_str()
        })
        .collect();
    let find = |name: &str| {
        r.occurrences()
            .iter()
            .position(|q| {
                r.base().base().readings().instances()[q.position.instance]
                    .declaration()
                    .name
                    == name
            })
            .unwrap()
    };
    assert_eq!(names.len(), 3);
    for (name, constant, epsilon, holds) in [
        ("Selected.zero", None, "\"2\"", false),
        ("Selected.one", Some("\"-1\""), "\"1\"", false),
        ("Selected.two", Some("\"-2\""), "\"0\"", true),
    ] {
        let q = &r.occurrences()[find(name)];
        let mut expected = vec![];
        if let Some(c) = constant {
            expected.push((vec![], c.to_string()));
        }
        expected.push((vec![0], "\"1\"".into()));
        assert_eq!(terms(q.nu.as_ref().unwrap()), expected);
        assert_eq!(number(&q.epsilon), Some(epsilon.into()));
        assert_eq!(q.evaluated_nu, q.epsilon);
        assert_eq!(q.epsilon_constant, q.residual_constant);
        assert!(q.epsilon_constant.is_some());
        assert_eq!(q.component_holds, Some(holds));
        assert!(!q.steps.is_empty());
        assert!(q.epsilon_producer.is_some());
    }
    let mut actual = ring.required_generators.clone();
    actual.sort();
    let mut expected = vec![find("Selected.zero"), find("Selected.one")];
    expected.sort();
    assert_eq!(actual, expected);
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn products_negation_aliases_and_helper_calls_normalize_original_derivations() {
    let i = inputs(
        "view square(c:Part):Z=c.quantity*c.quantity;law required poly(c:Part):let x=c.quantity in -(x-1)*(x+1)+square(c)=1;",
    );
    let r = run(i.clone());
    let q = &r.occurrences()[0];
    assert_eq!(q.status, S::Ready);
    assert!(q.nu.as_ref().unwrap().terms.is_empty());
    assert_eq!(r.rings()[0].symbols.len(), 1);
    assert!(r.rings()[0].symbols[0].readings.len() >= 2);
    assert_eq!(
        terms(q.left.as_ref().unwrap()),
        vec![(vec![], "\"1\"".into())]
    );
    assert_eq!(number(&q.epsilon), Some("\"0\"".into()));
    assert_eq!(q.component_holds, Some(true));
    assert!(
        q.steps
            .iter()
            .any(|s| terms(&s.polynomial) == vec![(vec![0, 0], "\"1\"".into())])
    );
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn equal_values_in_distinct_subject_slots_are_distinct_shared_symbols() {
    let map=fixture::A.replace("{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}","{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"},{\"id\":\"q\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}")
        .replace("\"atoms\":[","\"atoms\":[{\"id\":\"owner-q\",\"subject\":\"q\",\"field\":\"Pattern.Part.owner\",\"value\":[\"v\",\"root\"],\"origin\":\"model\"},{\"id\":\"quantity-q\",\"subject\":\"q\",\"field\":\"Pattern.Part.quantity\",\"value\":\"2\",\"origin\":\"model\"},");
    let i = inputs_with(fixture::D, "law required same(c:Part):c.quantity=2;", &map);
    let r = run(i.clone());
    assert_eq!(r.rings()[0].symbols.len(), 2);
    assert_ne!(r.rings()[0].symbols[0].slot, r.rings()[0].symbols[1].slot);
    assert_eq!(r.rings()[0].symbols[0].value, r.rings()[0].symbols[1].value);
    assert_eq!(r.occurrences().len(), 2);
    assert_ne!(r.occurrences()[0].nu, r.occurrences()[1].nu);
    assert!(
        r.occurrences()
            .iter()
            .all(|q| q.component_holds == Some(true))
    );
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn nested_tuple_components_and_projection_keep_z_q_fp_rings_separate() {
    let i = inputs(
        "view half():Q=rat(1,2);view field():Fp(5)=3;law optional axes(c:Part):((c.quantity,(half(),field())),(c.quantity,7).0)=((0,(rat(1,3),1)),0);",
    );
    let r = run(i.clone());
    assert_eq!(r.status(), S::Ready);
    assert_eq!(r.rings().len(), 3);
    assert_eq!(r.occurrences().len(), 4);
    let q = r.occurrences();
    assert_eq!(
        q.iter().map(|v| v.component.clone()).collect::<Vec<_>>(),
        [vec![0, 0], vec![0, 1, 0], vec![0, 1, 1], vec![1]]
    );
    assert_eq!(q[0].nu, q[3].nu);
    assert_eq!(r.rings()[q[0].ring.unwrap()].symbols.len(), 1);
    assert_eq!(number(&q[0].epsilon), Some("\"2\"".into()));
    assert_eq!(number(&q[1].epsilon), Some("[\"1\",\"6\"]".into()));
    assert_eq!(number(&q[2].epsilon), Some("\"2\"".into()));
    assert_eq!(q[0].ty, Type::Z);
    assert_eq!(q[1].ty, Type::Q);
    assert_eq!(q[2].ty, Type::Fp("5".into()));
    assert!(r.rings().iter().all(|v| v.required_generators.is_empty()));
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn all_finite_parameter_rows_share_primitive_symbols_and_keep_concrete_coefficients() {
    let i = inputs("law required family(c:Part,b:Bool):c.quantity+(if b then 1 else 0)=2;");
    let r = run(i.clone());
    assert_eq!(r.occurrences().len(), 2);
    assert_eq!(r.rings()[0].symbols.len(), 1);
    assert_eq!(r.rings()[0].required_generators, [0, 1]);
    for (q, (constant, epsilon, holds)) in r
        .occurrences()
        .iter()
        .zip([("\"-2\"", "\"0\"", true), ("\"-1\"", "\"1\"", false)])
    {
        assert_eq!(
            terms(q.nu.as_ref().unwrap()),
            [(vec![], constant.into()), (vec![0], "\"1\"".into())]
        );
        assert_eq!(number(&q.epsilon), Some(epsilon.into()));
        assert_eq!(q.component_holds, Some(holds));
        assert_eq!(q.status, S::Ready);
    }
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn missing_integer_slot_keeps_symbolic_nu_but_no_epsilon_or_total_substitution() {
    let map = fixture::A
        .lines()
        .filter(|l| !l.contains("\"quantity-p\""))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]");
    let i = inputs_with(
        fixture::D,
        "law required amount(c:Part):c.quantity=1;",
        &map,
    );
    let r = run(i.clone());
    let q = &r.occurrences()[0];
    assert!(r.is_complete());
    assert_eq!(r.status(), S::Undetermined);
    assert_eq!(q.status, S::Undetermined);
    assert_eq!(r.rings()[0].symbols.len(), 1);
    assert!(r.rings()[0].symbols[0].value.is_none());
    assert!(r.rings()[0].evaluation_images.is_none());
    assert!(q.epsilon_constant.is_none());
    assert_eq!(
        terms(q.nu.as_ref().unwrap()),
        [(vec![], "\"-1\"".into()), (vec![0], "\"1\"".into())]
    );
    assert!(q.epsilon.is_none());
    assert!(q.evaluated_nu.is_none());
    assert!(q.component_holds.is_none());
    assert_eq!(r.rings()[0].required_generators, [0]);
    assert!(r.rings()[0].symbols[0].readings[0].fact.atom.is_none());
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn pure_false_and_state_dependent_guards_never_enter_required_ideal() {
    let i = inputs(
        "law required no(c:Part) when false:c.quantity=0;law required dynamic(c:Part) when c.quantity>0:c.quantity=0;law required yes(c:Part) when true:c.quantity=2;",
    );
    let r = run(i.clone());
    let find = |name: &str| {
        r.occurrences()
            .iter()
            .position(|q| {
                r.base().base().readings().instances()[q.position.instance]
                    .declaration()
                    .name
                    == name
            })
            .unwrap()
    };
    assert_eq!(r.rings()[0].required_generators, [find("Selected.yes")]);
    let no = &r.occurrences()[find("Selected.no")];
    assert_eq!(no.guard, G::AlwaysFalse);
    assert_eq!(no.status, S::NotApplicable);
    assert_eq!(number(&no.residual), Some("\"0\"".into()));
    let dynamic = &r.occurrences()[find("Selected.dynamic")];
    assert_eq!(dynamic.guard, G::StateDependent);
    assert_eq!(dynamic.status, S::UnsupportedAlgorithm);
    assert!(dynamic.nu.is_some());
    assert_eq!(number(&dynamic.epsilon), Some("\"2\"".into()));
    assert_eq!(r.status(), S::UnsupportedAlgorithm);
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn state_dependent_piecewise_expression_is_not_its_observed_constant() {
    let i = inputs(
        "law required branching(c:Part):(if c.quantity>0 then c.quantity else 0)=0;law optional predicate(c:Part):c.quantity>0;",
    );
    let r = run(i.clone());
    assert_eq!(r.status(), S::UnsupportedAlgorithm);
    assert_eq!(r.occurrences().len(), 2);
    for q in r.occurrences() {
        assert_eq!(q.status, S::UnsupportedAlgorithm);
        assert!(q.nu.is_none());
    }
    assert!(r.rings().iter().all(|r| r.required_generators.is_empty()));
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn outside_selected_object_retains_original_uniform_without_fabricated_raw_equation() {
    let i = inputs("law required onlyRoot(a:Root,b:Bool):2=1;");
    let r =
        object_equation_presentation(i.clone(), "Selected", "v", "root", 1, &mut quiet()).unwrap();
    assert_eq!(r.object(), 1);
    assert_eq!(r.occurrences().len(), 1);
    let q = &r.occurrences()[0];
    assert_eq!(q.guard, G::OutsideObject);
    assert_eq!(q.status, S::NotApplicable);
    assert_eq!(q.row, None);
    assert!(q.nu.is_none());
    assert!(q.epsilon.is_none());
    assert_eq!(number(&q.residual), Some("\"0\"".into()));
    assert!(r.rings()[0].required_generators.is_empty());
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn empty_law_and_empty_parameter_domains_do_not_invent_occurrences() {
    for law in [
        "view value(c:Part):Z=c.quantity;",
        "law required empty(c:Part,v:Vacant):c.quantity=0;",
    ] {
        let i = inputs(law);
        let r = run(i.clone());
        assert!(r.is_complete());
        assert_eq!(r.status(), S::Ready);
        assert!(r.occurrences().is_empty());
        assert!(r.rings().is_empty());
        r.recheck(i, &mut quiet()).unwrap();
    }
}
#[test]
fn changed_current_input_and_invalid_object_are_rejected() {
    let i = inputs("law required amount(c:Part):c.quantity=0;");
    let r = run(i.clone());
    let changed = inputs("law required amount(c:Part):c.quantity=1;");
    assert!(r.recheck(changed, &mut quiet()).is_err());
    assert!(matches!(
        object_equation_presentation(i, "Selected", "v", "root", 2, &mut quiet()),
        Err(EquationPresentationFailure::Selection(_))
    ));
}
#[test]
fn fixed_stops_keep_completed_polynomials_original_counterexamples_and_final_completion() {
    use archsig::{
        construction::ConstructionFailure,
        observed::control::{Checkpoint as C, Resource, StopReason},
        result::Signal,
    };
    use std::{cell::RefCell, rc::Rc};
    let i = inputs(
        "law required first(c:Part) when true or c.quantity>0:c.quantity=0;law required second(c:Part) when c.quantity-c.quantity=0:c.quantity*c.quantity=1;",
    );
    let baseline = run(i.clone());
    for recheck in [false, true] {
        let history = Rc::new(RefCell::new(Vec::new()));
        let h = history.clone();
        let mut traced = Control::new(Limits::default(), move |p| {
            h.borrow_mut().push(p);
            Usage::default()
        });
        if recheck {
            baseline.recheck(i.clone(), &mut traced).unwrap();
        } else {
            object_equation_presentation(i.clone(), "Selected", "v", "root", 0, &mut traced)
                .unwrap();
        }
        for at in [C::EquationPresentation, C::EquationPresentationRow] {
            let count = history.borrow().iter().filter(|p| **p == at).count();
            assert!(count > 0);
            for nth in [1, count] {
                for mode in 0..4 {
                    let hits = Rc::new(RefCell::new(0));
                    let h = hits.clone();
                    let probes = Rc::new(RefCell::new(0));
                    let p = probes.clone();
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
                    let mut c = Control::new(
                        Limits {
                            time_ms: (mode == 0).then_some(1),
                            memory_mib: (mode == 1).then_some(1),
                        },
                        move |point| {
                            *p.borrow_mut() += 1;
                            if point == at {
                                *h.borrow_mut() += 1;
                            }
                            if point == at && *h.borrow() == nth {
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
                        },
                    );
                    let f = if recheck {
                        baseline.recheck(i.clone(), &mut c).unwrap_err()
                    } else {
                        object_equation_presentation(i.clone(), "Selected", "v", "root", 0, &mut c)
                            .unwrap_err()
                    };
                    let EquationPresentationFailure::Reading {
                        cause: ConstructionFailure::Stopped(reason),
                        partial,
                    } = f
                    else {
                        panic!("new presentation stage")
                    };
                    assert_eq!(reason, expected);
                    for (n, q) in partial.occurrences().iter().enumerate() {
                        assert_eq!(q, &baseline.occurrences()[n]);
                        assert_eq!(q.component_holds, Some(false));
                        assert!(q.epsilon.is_some());
                        assert!(q.nu.is_some());
                    }
                    if at == C::EquationPresentationRow && nth == 1 {
                        assert_eq!(partial.occurrences().len(), 1);
                        assert!(!partial.is_complete());
                    }
                    if at == C::EquationPresentationRow && nth == count {
                        assert_eq!(partial.occurrences(), baseline.occurrences());
                        assert_eq!(partial.rings(), baseline.rings());
                        assert!(partial.is_complete());
                    }
                    if at == C::EquationPresentation && nth == count {
                        assert!(partial.is_complete());
                    }
                    let before = *probes.borrow();
                    assert_eq!(c.checkpoint(C::EquationPresentation), Err(expected));
                    assert_eq!(*probes.borrow(), before);
                }
            }
        }
    }
}

#[test]
fn primitive_q_and_fp_coefficients_use_the_declared_rings_and_normalize_exactly() {
    for (ty, wire, law, epsilon, constant) in [
        (
            "\"Q\"",
            "[\"1\",\"2\"]",
            "law required scale(c:Part):c.quantity+c.quantity=rat(1,3);",
            "[\"2\",\"3\"]",
            "[\"-1\",\"3\"]",
        ),
        (
            "[\"Fp\",\"5\"]",
            "\"4\"",
            "law required scale(c:Part):c.quantity+c.quantity=1;",
            "\"2\"",
            "\"4\"",
        ),
    ] {
        let d = fixture::D.replace("\"type\":\"Z\"", &format!("\"type\":{ty}"));
        let map = fixture::A.replace("\"value\":\"2\"", &format!("\"value\":{wire}"));
        let i = inputs_with(&d, law, &map);
        let r = run(i.clone());
        let q = &r.occurrences()[0];
        assert_eq!(q.status, S::Ready);
        assert_eq!(r.rings()[0].symbols.len(), 1);
        assert_eq!(
            terms(q.nu.as_ref().unwrap()),
            [
                (vec![], constant.into()),
                (
                    vec![0],
                    if ty == "\"Q\"" {
                        "[\"2\",\"1\"]".into()
                    } else {
                        "\"2\"".into()
                    }
                )
            ]
        );
        assert_eq!(number(&q.epsilon), Some(epsilon.into()));
        assert_eq!(q.evaluated_nu, q.epsilon);
        r.recheck(i, &mut quiet()).unwrap();
    }
}
#[test]
fn primitive_tuple_positions_are_shared_separately_even_with_equal_values() {
    let d = fixture::D.replace("\"type\":\"Z\"", "\"type\":[\"Tuple\",\"Z\",\"Z\"]");
    let map = fixture::A.replace("\"value\":\"2\"", "\"value\":[\"2\",\"2\"]");
    let i = inputs_with(
        &d,
        "law required pair(c:Part):c.quantity=(0,0);law optional first(c:Part):c.quantity.0=0;",
        &map,
    );
    let r = run(i.clone());
    assert_eq!(r.status(), S::Ready);
    assert_eq!(r.rings()[0].symbols.len(), 2);
    let a = &r.rings()[0].symbols[0];
    let b = &r.rings()[0].symbols[1];
    assert_eq!(a.slot.component, [0]);
    assert_eq!(b.slot.component, [1]);
    assert_eq!(a.value, b.value);
    assert_ne!(a.slot, b.slot);
    assert_eq!(r.occurrences().len(), 3);
    assert!(
        r.occurrences()
            .iter()
            .all(|q| number(&q.epsilon) == Some("\"2\"".into()))
    );
    assert!(
        r.occurrences()
            .iter()
            .all(|q| q.component_holds == Some(false))
    );
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn finite_fp_parameter_domain_keeps_all_five_coefficients_in_one_shared_ring() {
    let d = fixture::D.replace("\"type\":\"Z\"", "\"type\":[\"Fp\",\"5\"]");
    let map = fixture::A.replace("\"value\":\"2\"", "\"value\":\"4\"");
    let i = inputs_with(
        &d,
        "law required family(c:Part,n:Fp(5)):c.quantity+n=0;",
        &map,
    );
    let r = run(i.clone());
    assert_eq!(r.status(), S::Ready);
    assert_eq!(r.rings().len(), 1);
    assert_eq!(r.rings()[0].ty, Type::Fp("5".into()));
    assert_eq!(r.rings()[0].symbols.len(), 1);
    assert_eq!(r.occurrences().len(), 5);
    assert_eq!(r.rings()[0].required_generators, [0, 1, 2, 3, 4]);
    for (n, q) in r.occurrences().iter().enumerate() {
        let mut expected = vec![];
        if n > 0 {
            expected.push((vec![], format!("\"{n}\"")));
        }
        expected.push((vec![0], "\"1\"".into()));
        assert_eq!(terms(q.nu.as_ref().unwrap()), expected);
        assert_eq!(number(&q.epsilon), Some(format!("\"{}\"", (4 + n) % 5)));
        assert_eq!(q.component_holds, Some(n == 1));
    }
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn changed_provenance_keeps_slot_identity_but_is_rejected_as_stale_evidence() {
    let law = "law required amount(c:Part):c.quantity=0;";
    let i = inputs(law);
    let r = run(i.clone());
    let changed = inputs_with(
        fixture::D,
        law,
        &fixture::A.replace("fixture-r1", "different-source"),
    );
    let fresh = run(changed.clone());
    assert_eq!(r.rings(), fresh.rings());
    assert_eq!(r.occurrences(), fresh.occurrences());
    assert!(r.recheck(changed, &mut quiet()).is_err());
    assert_eq!(
        r.base().base().readings().construction(),
        fresh.base().base().readings().construction()
    );
}

#[test]
fn missing_boolean_guard_cases_are_not_global_true_required_generators() {
    let d = fixture::D.replace("\"type\":\"Z\"", "\"type\":\"Bool\"");
    let map = fixture::A
        .lines()
        .filter(|l| !l.contains("\"quantity-p\""))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]");
    let i = inputs_with(
        &d,
        "law required guarded(c:Part) when c.quantity:2=0;",
        &map,
    );
    let r = run(i.clone());
    assert_eq!(r.occurrences().len(), 2);
    assert!(r.rings().iter().all(|v| v.required_generators.is_empty()));
    for q in r.occurrences() {
        assert_eq!(q.guard, G::StateDependent);
        assert_eq!(q.status, S::UnsupportedAlgorithm);
    }
    assert_eq!(r.status(), S::UnsupportedAlgorithm);
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn two_distinct_symbols_commute_and_cancel_with_original_support_retained() {
    let map=fixture::A.replace("{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}","{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"},{\"id\":\"q\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}")
        .replace("\"atoms\":[","\"atoms\":[{\"id\":\"owner-q\",\"subject\":\"q\",\"field\":\"Pattern.Part.owner\",\"value\":[\"v\",\"root\"],\"origin\":\"model\"},{\"id\":\"quantity-q\",\"subject\":\"q\",\"field\":\"Pattern.Part.quantity\",\"value\":\"3\",\"origin\":\"model\"},");
    let i = inputs_with(
        fixture::D,
        "law required commute(c:Part,d:Part):c.quantity*d.quantity-d.quantity*c.quantity=0;",
        &map,
    );
    let r = run(i.clone());
    assert_eq!(r.status(), S::Ready);
    assert_eq!(r.occurrences().len(), 4);
    assert_eq!(r.rings()[0].symbols.len(), 2);
    assert_eq!(r.rings()[0].required_generators.len(), 4);
    assert!(
        r.occurrences()
            .iter()
            .all(|q| q.nu.as_ref().unwrap().terms.is_empty()
                && q.component_holds == Some(true)
                && number(&q.epsilon) == Some("\"0\"".into()))
    );
    assert!(
        r.occurrences()
            .iter()
            .flat_map(|q| &q.steps)
            .any(|s| terms(&s.polynomial) == vec![(vec![0, 1], "\"1\"".into())])
    );
    r.recheck(i, &mut quiet()).unwrap();
}
fn two_subjects() -> String {
    fixture::A.replace("{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}","{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"},{\"id\":\"q\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}")
        .replace("\"atoms\":[","\"atoms\":[{\"id\":\"owner-q\",\"subject\":\"q\",\"field\":\"Pattern.Part.owner\",\"value\":[\"v\",\"root\"],\"origin\":\"model\"},{\"id\":\"quantity-q\",\"subject\":\"q\",\"field\":\"Pattern.Part.quantity\",\"value\":\"3\",\"origin\":\"model\"},")
}
fn binding(
    r: &EquationPresentation,
    q: &archsig::construction::readings::EquationOccurrence,
    name: &str,
) -> String {
    r.base().base().readings().instances()[q.position.instance]
        .bindings()
        .iter()
        .find(|b| b.parameter().name == name)
        .unwrap()
        .subject()
        .subject
        .clone()
}
#[test]
fn state_dependent_reference_base_is_not_observed_slot_even_through_alias_helper_and_projection() {
    for law in [
        "law required select(c:Part,d:Part):(if c.quantity>0 then c else d).quantity=0;",
        "law required select(c:Part,d:Part):let r=(if c.quantity>0 then c else d) in r.quantity=0;",
        "view choose(a:Part,b:Part):Part=if a.quantity>0 then a else b;law required select(c:Part,d:Part):choose(c,d).quantity=0;",
        "law required select(c:Part,d:Part):((if c.quantity>0 then c else d),c).0.quantity=0;",
        "view carryRef(a:Part):Part=a;law required select(c:Part,d:Part):carryRef(if c.quantity>0 then c else d).quantity=0;",
    ] {
        let i = inputs_with(fixture::D, law, &two_subjects());
        let r = run(i.clone());
        assert_eq!(r.occurrences().len(), 4);
        assert_eq!(r.status(), S::UnsupportedAlgorithm);
        for (index, q) in r.occurrences().iter().enumerate() {
            let same = binding(&r, q, "c") == binding(&r, q, "d");
            assert_eq!(
                q.status,
                if same {
                    S::Ready
                } else {
                    S::UnsupportedAlgorithm
                }
            );
            assert_eq!(q.nu.is_some(), same);
            assert_eq!(
                r.rings()[q.ring.unwrap()]
                    .required_generators
                    .contains(&index),
                same
            );
            assert!(q.evaluation.is_some());
            assert!(q.epsilon.is_some());
        }
        r.recheck(i, &mut quiet()).unwrap();
        let changed = inputs_with(
            fixture::D,
            law,
            &two_subjects().replace("\"value\":\"2\"", "\"value\":\"0\""),
        );
        let fresh = run(changed);
        let q = fresh
            .occurrences()
            .iter()
            .find(|q| binding(&fresh, q, "c") == "p" && binding(&fresh, q, "d") == "q")
            .unwrap();
        assert_eq!(q.status, S::UnsupportedAlgorithm);
        assert!(q.nu.is_none());
        assert_eq!(number(&q.epsilon), Some("\"3\"".into()));
    }
}
#[test]
fn fixed_reference_binders_helpers_and_primitive_chains_keep_polynomial_fields() {
    let d=fixture::D.replace("\"meaning\":\"数量。\"}","\"meaning\":\"数量。\"},{\"name\":\"peer\",\"type\":[\"Ref\",\"Pattern.Part\"],\"meaning\":\"固定参照。\"}");
    let map=fixture::A.replace("\"atoms\":[","\"atoms\":[{\"id\":\"peer-p\",\"subject\":\"p\",\"field\":\"Pattern.Part.peer\",\"value\":[\"v\",\"p\"],\"origin\":\"model\"},");
    for law in [
        "law required fixed(c:Part):(let r=c in r).quantity=0;",
        "view carryRef(a:Part):Part=a;law required fixed(c:Part):carryRef(c).quantity=0;",
        "law required fixed(c:Part):c.peer.quantity=0;",
        "law required fixed(c:Part):(c,c).0.quantity=0;",
    ] {
        let i = inputs_with(&d, law, &map);
        let r = run(i.clone());
        let q = &r.occurrences()[0];
        assert_eq!(q.status, S::Ready);
        assert_eq!(r.rings()[0].symbols.len(), 1);
        assert_eq!(r.rings()[0].symbols[0].slot.subject, "p");
        assert_eq!(terms(q.nu.as_ref().unwrap()), [(vec![0], "\"1\"".into())]);
        assert_eq!(number(&q.epsilon), Some("\"2\"".into()));
        r.recheck(i, &mut quiet()).unwrap();
    }
}
#[test]
fn unused_bindings_arguments_and_projected_positions_keep_full_shared_support() {
    let i = inputs(
        "view ignore(x:Z):Z=2;law required outside(c:Part):let unused=c.quantity in 2=2;law required inside(c:Part):(let unused=c.quantity in 2)=2;law optional helper(c:Part):ignore(c.quantity)=2;law optional projection(c:Part):(2,c.quantity).0=2;",
    );
    let r = run(i.clone());
    assert_eq!(r.status(), S::Ready);
    assert_eq!(r.occurrences().len(), 4);
    assert_eq!(r.rings()[0].symbols.len(), 1);
    let symbol = &r.rings()[0].symbols[0];
    assert_eq!(symbol.slot.subject, "p");
    assert_eq!(symbol.readings.len(), 4);
    assert_eq!(number(&symbol.value), Some("\"2\"".into()));
    for q in r.occurrences() {
        assert!(q.nu.as_ref().unwrap().terms.is_empty());
        assert_eq!(q.component_holds, Some(true));
        assert_eq!(number(&q.epsilon), Some("\"0\"".into()));
        assert!(
            symbol
                .readings
                .iter()
                .any(|v| v.position == q.position && v.row == q.row && v.case == q.case)
        );
    }
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn missing_unused_support_remains_unknown_even_when_the_constant_equation_holds() {
    let map = fixture::A
        .lines()
        .filter(|l| !l.contains("\"quantity-p\""))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]");
    let i = inputs_with(
        fixture::D,
        "law required unused(c:Part):(let x=c.quantity in 2)=2;",
        &map,
    );
    let r = run(i.clone());
    assert_eq!(r.status(), S::Undetermined);
    assert_eq!(r.rings()[0].symbols.len(), 1);
    assert!(r.rings()[0].symbols[0].value.is_none());
    assert!(r.rings()[0].evaluation_images.is_none());
    assert!(r.rings()[0].symbols[0].readings[0].fact.atom.is_none());
    let q = &r.occurrences()[0];
    assert!(q.nu.as_ref().unwrap().terms.is_empty());
    assert_eq!(q.component_holds, Some(true));
    assert_eq!(number(&q.epsilon), Some("\"0\"".into()));
    assert_eq!(q.status, S::Undetermined);
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn nonnumeric_false_guard_and_outside_object_are_not_applicable() {
    let i = inputs("law required off(c:Part) when false:c.quantity>0;");
    let r = run(i.clone());
    assert_eq!(r.status(), S::Ready);
    assert_eq!(r.occurrences()[0].status, S::NotApplicable);
    assert_eq!(r.occurrences()[0].guard, G::AlwaysFalse);
    assert!(r.occurrences()[0].nu.is_none());
    assert!(r.rings().is_empty());
    r.recheck(i, &mut quiet()).unwrap();
    let i = inputs("law required rootOnly(a:Root):false;");
    let r =
        object_equation_presentation(i.clone(), "Selected", "v", "root", 1, &mut quiet()).unwrap();
    assert_eq!(r.status(), S::Ready);
    assert_eq!(r.occurrences()[0].status, S::NotApplicable);
    assert_eq!(r.occurrences()[0].guard, G::OutsideObject);
    assert!(r.occurrences()[0].nu.is_none());
    assert!(r.rings().is_empty());
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn unused_state_dependent_reference_keeps_each_reading_without_symbolizing_its_value() {
    let boolean_definition = fixture::D.replace(
        "\"meaning\":\"数量。\"}",
        "\"meaning\":\"数量。\"},{\"name\":\"enabled\",\"type\":\"Bool\",\"meaning\":\"選択。\"}",
    );
    let boolean_map=two_subjects().replace("\"atoms\":[","\"atoms\":[{\"id\":\"enabled-p\",\"subject\":\"p\",\"field\":\"Pattern.Part.enabled\",\"value\":false,\"origin\":\"model\"},{\"id\":\"enabled-q\",\"subject\":\"q\",\"field\":\"Pattern.Part.enabled\",\"value\":true,\"origin\":\"model\"},");
    for (definition, map, condition) in [
        (
            fixture::D,
            two_subjects().replace("\"value\":\"2\"", "\"value\":\"0\""),
            "c.quantity>0",
        ),
        (boolean_definition.as_str(), boolean_map, "c.enabled"),
    ] {
        for template in [
            "law required select(c:Part,d:Part):let unused=(if <COND> then c else d).quantity in 2=2;",
            "law required select(c:Part,d:Part):(let unused=(if <COND> then c else d).quantity in 2)=2;",
            "view ignore(x:Z):Z=2;law required select(c:Part,d:Part):ignore((if <COND> then c else d).quantity)=2;",
            "law required select(c:Part,d:Part):(2,(if <COND> then c else d).quantity).0=2;",
        ] {
            let i = inputs_with(definition, &template.replace("<COND>", condition), &map);
            let r = run(i.clone());
            assert_eq!(r.status(), S::Ready);
            assert_eq!(r.occurrences().len(), 4);
            assert_eq!(r.rings()[0].symbols.len(), 2);
            assert_eq!(r.rings()[0].required_generators.len(), 4);
            for q in r.occurrences() {
                let subject = if binding(&r, q, "c") == "p" {
                    binding(&r, q, "d")
                } else {
                    binding(&r, q, "c")
                };
                let symbol = r.rings()[q.ring.unwrap()]
                    .symbols
                    .iter()
                    .find(|s| s.slot.subject == subject)
                    .unwrap();
                assert!(
                    symbol
                        .readings
                        .iter()
                        .any(|read| read.position == q.position
                            && read.row == q.row
                            && read.case == q.case
                            && read.fact.subject == subject
                            && read.fact.field.as_deref() == Some("Pattern.Part.quantity"))
                );
                assert!(q.nu.as_ref().unwrap().terms.is_empty());
                assert_eq!(q.component_holds, Some(true));
                assert_eq!(number(&q.epsilon), Some("\"0\"".into()));
            }
            r.recheck(i, &mut quiet()).unwrap();
        }
        // 支持の記録だけでは、実際に使う状態依存fieldを単一記号へ置換しない。
        let i = inputs_with(
            definition,
            &format!(
                "law required select(c:Part,d:Part):(if {condition} then c else d).quantity=0;"
            ),
            &map,
        );
        let r = run(i.clone());
        for q in r.occurrences() {
            if binding(&r, q, "c") != binding(&r, q, "d") {
                assert_eq!(q.status, S::UnsupportedAlgorithm);
                assert!(q.nu.is_none());
            }
        }
        r.recheck(i, &mut quiet()).unwrap();
    }
}

#[test]
fn missing_reference_completion_is_not_a_fixed_polynomial_slot() {
    let d=fixture::D.replace("\"meaning\":\"数量。\"}","\"meaning\":\"数量。\"},{\"name\":\"peer\",\"type\":[\"Ref\",\"Pattern.Part\"],\"meaning\":\"参照。\"}");
    for law in [
        "law required select(c:Part):c.peer.quantity=0;",
        "law required select(c:Part):(c.peer).quantity=0;",
        "law required select(c:Part):let r=c.peer in r.quantity=0;",
        "view carryRef(a:Part):Part=a;law required select(c:Part):carryRef(c.peer).quantity=0;",
        "law required select(c:Part):(c.peer,c).0.quantity=0;",
    ] {
        let i = inputs_with(&d, law, &two_subjects());
        let r = run(i.clone());
        assert_eq!(r.status(), S::UnsupportedAlgorithm);
        assert!(r.occurrences().len() >= 4);
        for q in r.occurrences() {
            assert_eq!(q.status, S::UnsupportedAlgorithm);
            assert!(q.nu.is_none());
            assert!(q.evaluation.is_some());
            assert!(q.epsilon.is_some());
            assert!(r.rings()[q.ring.unwrap()].required_generators.is_empty());
        }
        let values: std::collections::BTreeSet<_> = r
            .occurrences()
            .iter()
            .filter_map(|q| number(&q.epsilon))
            .collect();
        assert_eq!(
            values,
            std::collections::BTreeSet::from(["\"2\"".into(), "\"3\"".into()])
        );
        r.recheck(i, &mut quiet()).unwrap();
    }
}
#[test]
fn logical_and_normalized_numeric_guard_constants_keep_required_ideals_and_support() {
    for (prefix, expression, truth) in [
        ("", "true or c.quantity>0", true),
        ("", "c.quantity>0 or true", true),
        ("", "false and c.quantity>0", false),
        ("", "c.quantity>0 and false", false),
        ("", "false implies c.quantity>0", true),
        ("", "c.quantity>0 implies true", true),
        ("", "not (false and c.quantity>0)", true),
        ("", "let ignored=c.quantity in true", true),
        ("", "(true,c.quantity>0).0", true),
        ("", "if c.quantity>0 then true else true", true),
        ("view on(a:Part):Bool=true or a.quantity>0;", "on(c)", true),
        ("", "c.quantity-c.quantity=0", true),
        ("", "c.quantity-c.quantity=1", false),
        ("", "c.quantity+1>c.quantity", true),
        ("", "c.quantity*c.quantity-c.quantity*c.quantity<=0", true),
        (
            "",
            "(c.quantity,c.quantity+1)=(c.quantity,c.quantity+2)",
            false,
        ),
    ] {
        let body = format!("{prefix}law required guarded(c:Part) when {expression}:c.quantity=0;");
        let i = inputs(&body);
        let r = run(i.clone());
        assert_eq!(r.status(), S::Ready, "{expression}");
        let q = &r.occurrences()[0];
        assert_eq!(
            q.guard,
            if truth { G::AlwaysTrue } else { G::AlwaysFalse },
            "{expression}"
        );
        assert_eq!(
            q.status,
            if truth { S::Ready } else { S::NotApplicable },
            "{expression}"
        );
        assert_eq!(number(&q.epsilon), Some("\"2\"".into()));
        assert_eq!(
            number(&q.residual),
            Some(if truth { "\"2\"" } else { "\"0\"" }.into())
        );
        assert_eq!(
            r.rings()[0].required_generators,
            if truth { vec![0] } else { vec![] }
        );
        assert_eq!(r.rings()[0].symbols.len(), 1);
        assert!(!r.rings()[0].symbols[0].readings.is_empty());
        assert_eq!(terms(q.nu.as_ref().unwrap()), [(vec![0], "\"1\"".into())]);
        r.recheck(i, &mut quiet()).unwrap();
    }
}
#[test]
fn current_guard_truth_and_distinct_slots_do_not_prove_a_global_constant() {
    for guard in [
        "c.quantity>0",
        "c.quantity-c.quantity=0 and c.quantity>0",
        "c.quantity=d.quantity",
        "c.quantity+1=d.quantity+1",
    ] {
        let i = inputs_with(
            fixture::D,
            &format!("law required guarded(c:Part,d:Part) when {guard}:c.quantity=0;"),
            &two_subjects(),
        );
        let r = run(i.clone());
        for q in r.occurrences() {
            let same = binding(&r, q, "c") == binding(&r, q, "d");
            let tautology = guard.contains("d.quantity") && same;
            assert_eq!(
                q.guard,
                if tautology {
                    G::AlwaysTrue
                } else {
                    G::StateDependent
                },
                "{guard}"
            );
            assert_eq!(
                q.status,
                if tautology {
                    S::Ready
                } else {
                    S::UnsupportedAlgorithm
                }
            );
        }
        let expected: Vec<_> = r
            .occurrences()
            .iter()
            .enumerate()
            .filter(|(_, q)| q.guard == G::AlwaysTrue)
            .map(|(i, _)| i)
            .collect();
        assert_eq!(r.rings()[0].required_generators, expected);
        r.recheck(i, &mut quiet()).unwrap();
    }
}

#[test]
fn missing_boolean_guard_constants_keep_each_completion_and_original_support() {
    let d = fixture::D.replace(
        "\"meaning\":\"数量。\"}",
        "\"meaning\":\"数量。\"},{\"name\":\"enabled\",\"type\":\"Bool\",\"meaning\":\"選択。\"}",
    );
    for (guard, truth) in [("true or c.enabled", true), ("false and c.enabled", false)] {
        let i = inputs_with(
            &d,
            &format!("law required guarded(c:Part) when {guard}:c.quantity=0;"),
            fixture::A,
        );
        let r = run(i.clone());
        assert_eq!(r.status(), S::Ready);
        assert_eq!(r.occurrences().len(), 2);
        assert_eq!(
            r.rings()[0].required_generators,
            if truth { vec![0, 1] } else { vec![] }
        );
        for q in r.occurrences() {
            assert_eq!(q.guard, if truth { G::AlwaysTrue } else { G::AlwaysFalse });
            assert_eq!(q.status, if truth { S::Ready } else { S::NotApplicable });
            assert_eq!(
                number(&q.epsilon),
                if truth { Some("\"2\"".into()) } else { None }
            );
            if !truth {
                assert!(q.operands.is_empty());
                assert!(q.nu.is_none());
                assert!(q.component_holds.is_none());
            }
            assert_eq!(
                number(&q.residual),
                Some(if truth { "\"2\"" } else { "\"0\"" }.into())
            );
            let evaluation = r.base().base().evaluations()[q.position.instance].evaluation();
            let archsig::construction::readings::ObjectEvaluationOutcome::Evaluated(g) =
                evaluation.outcome()
            else {
                panic!("original evaluation")
            };
            use archsig::canonical::Json;
            fn missing_fact(j: &Json) -> bool {
                match j {
                    Json::Obj(o) => {
                        (o.get("field") == Some(&Json::str("Pattern.Part.enabled"))
                            && !o.contains_key("atom"))
                            || o.values().any(missing_fact)
                    }
                    Json::Arr(items) => items.iter().any(missing_fact),
                    _ => false,
                }
            }
            let wire = g.wire();
            let Json::Obj(object) = &wire else {
                panic!("original graph object")
            };
            let Some(Json::Arr(nodes)) = object.get("nodes") else {
                panic!("original graph nodes")
            };
            assert!(missing_fact(&nodes[q.evaluation.unwrap()]));
        }
        r.recheck(i, &mut quiet()).unwrap();
    }
}
#[test]
fn rational_and_prime_field_guard_normalization_uses_the_original_coefficient_ring() {
    for (ty, value, epsilon) in [
        (r#""Q""#, r#"["2","3"]"#, r#"["2","3"]"#),
        (r#"["Fp","5"]"#, r#""2""#, r#""2""#),
    ] {
        let d = fixture::D.replace(r#""type":"Z""#, &format!("\"type\":{ty}"));
        let map = fixture::A.replace(r#""value":"2""#, &format!("\"value\":{value}"));
        let i = inputs_with(
            &d,
            "law required on(c:Part) when c.quantity-c.quantity=0:c.quantity=0;law required off(c:Part) when c.quantity-c.quantity!=0:c.quantity=0;",
            &map,
        );
        let r = run(i.clone());
        assert_eq!(r.status(), S::Ready);
        assert_eq!(r.rings().len(), 1);
        let find = |guard| {
            r.occurrences()
                .iter()
                .enumerate()
                .find(|(_, q)| q.guard == guard)
                .unwrap()
        };
        let (on, q) = find(G::AlwaysTrue);
        assert_eq!(q.status, S::Ready);
        assert_eq!(number(&q.epsilon), Some(epsilon.into()));
        assert_eq!(r.rings()[0].required_generators, [on]);
        let (_, q) = find(G::AlwaysFalse);
        assert_eq!(q.status, S::NotApplicable);
        assert_eq!(number(&q.epsilon), Some(epsilon.into()));
        r.recheck(i, &mut quiet()).unwrap();
    }
}

#[test]
fn missing_integer_guard_cancellation_proves_truth_without_inventing_an_observation() {
    let map = fixture::A
        .lines()
        .filter(|l| !l.contains("\"quantity-p\""))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]");
    let i = inputs_with(
        fixture::D,
        "law required cancellation(c:Part) when c.quantity-c.quantity=0:2=2;",
        &map,
    );
    let r = run(i.clone());
    let q = &r.occurrences()[0];
    assert_eq!(q.guard, G::AlwaysTrue);
    assert_eq!(q.status, S::Undetermined);
    assert_eq!(q.component_holds, Some(true));
    assert_eq!(number(&q.epsilon), Some("\"0\"".into()));
    assert!(q.nu.as_ref().unwrap().terms.is_empty());
    assert_eq!(r.rings()[0].required_generators, [0]);
    assert!(r.rings()[0].evaluation_images.is_none());
    assert!(r.rings()[0].symbols[0].value.is_none());
    assert!(r.rings()[0].symbols[0].readings[0].fact.atom.is_none());
    r.recheck(i, &mut quiet()).unwrap();
}
