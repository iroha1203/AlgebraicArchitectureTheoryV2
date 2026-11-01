use crate::common::object_view_compatibility_data as fixture;
use crate::common::quiet;
use archsig_common::control::Control;
use archsig_computation::observed::object_law_circuits::{
    LawCircuitDetector as Detector, LawCircuitsCondition as Condition, ObjectLawCircuits,
    ObjectLawCircuitsFailure, object_law_circuits,
};
use archsig_input::input::{CheckedInputs, InputSources, check_inputs};
use std::sync::Arc;
fn inputs(body: &str, map: &str) -> Arc<CheckedInputs> {
    inputs_with_definitions(fixture::D, body, map)
}
fn inputs_with_definitions(definitions: &str, body: &str, map: &str) -> Arc<CheckedInputs> {
    let d =
        archsig_input::definition::check_definitions(&[("definition0", definitions.as_bytes())])
            .unwrap();
    let digest = &d.vocabularies()["Pattern"].digest;
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
            &quiet(),
        )
        .unwrap_or_else(|f| panic!("{:?}", f.issues())),
    )
}

fn run(i: Arc<CheckedInputs>) -> ObjectLawCircuits {
    object_law_circuits(i, "Selected", "v", "root", &quiet()).unwrap()
}
fn missing() -> String {
    fixture::A
        .lines()
        .filter(|l| !l.contains("\"quantity-p\""))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]")
}
#[test]
fn tuple_zero_component_is_reject_and_only_nonzero_component_has_any_and_original_witness() {
    let i = inputs(
        "law required amount(c:Part):(c.quantity,3)=(2,0);",
        fixture::A,
    );
    let r = run(i.clone());
    assert!(r.is_complete());
    assert_eq!(r.condition(), &Condition::Ready);
    assert_eq!(r.circuits().len(), 4);
    for circuit in r.circuits() {
        assert!(circuit.complete);
        let expected = if circuit.component == [0] {
            Detector::Reject
        } else {
            Detector::Any
        };
        assert_eq!(circuit.detector, Some(expected));
        let p = &circuit.points[0];
        assert_eq!(p.when, Some(circuit.component == [1]));
        assert!(p.arguments.is_empty());
        for witness in &p.witnesses {
            assert_eq!(witness.when, p.when);
            let source = &r.base().evaluations()[witness.evaluation].rows[witness.row.unwrap()]
                .cases[witness.case];
            assert_eq!(witness.original_evaluation, source.evaluation);
            assert_eq!(witness.epsilon_producer, source.epsilon_producer);
            assert!(witness.epsilon_producer.is_some());
            assert_eq!(
                source.components[0]
                    .epsilon
                    .as_ref()
                    .unwrap()
                    .wire()
                    .canonical(),
                "\"0\""
            );
            assert_eq!(
                source.components[1]
                    .epsilon
                    .as_ref()
                    .unwrap()
                    .wire()
                    .canonical(),
                "\"3\""
            );
        }
        let pattern = circuit.pattern.as_ref().unwrap();
        assert_eq!(
            pattern.queries().count(),
            pattern.universe().len() + 2 * pattern.universe().len().pow(2)
        );
        assert_eq!(
            pattern,
            r.base().base().profiles().profiles()[circuit.position.object]
                .pattern()
                .unwrap()
        );
    }
    r.recheck(i, &quiet()).unwrap();
}
#[test]
fn all_bool_fp_arguments_make_exact_disjunction_with_typed_values() {
    use archsig_common::{canonical::Json, types::Type};
    let i = inputs(
        "law optional finite(c:Part,b:Bool,f:Fp(3)):(if b then f else 0)=0;",
        fixture::A,
    );
    let r = run(i.clone());
    assert_eq!(r.condition(), &Condition::Ready);
    for circuit in r.circuits() {
        assert_eq!(circuit.points.len(), 6);
        assert_eq!(circuit.ty, Type::Fp("3".into()));
        let Some(Detector::Exact(args)) = &circuit.detector else {
            panic!("exact")
        };
        assert_eq!(args.len(), 2);
        for (row, n) in args.iter().zip(["1", "2"]) {
            assert_eq!(row[0].wire(), Json::Bool(true));
            assert_eq!(row[1].wire().canonical(), format!("\"{n}\""));
        }
        assert_eq!(
            circuit
                .points
                .iter()
                .filter(|p| p.when == Some(true))
                .count(),
            2
        );
        assert!(circuit.points.iter().all(|p| p.when.is_some()));
    }
    r.recheck(i, &quiet()).unwrap();
}
#[test]
fn false_guard_and_outside_rows_reject_without_fabricating_raw_epsilon_or_arguments() {
    for body in [
        "law required guarded(c:Part,b:Bool) when false:c.quantity=0;",
        "law required outside(a:Root,b:Bool):2=1;",
    ] {
        let r = run(inputs(body, fixture::A));
        assert_eq!(
            r.condition(),
            if body.contains("guarded") {
                &Condition::Ready
            } else {
                &Condition::ConditionFailed
            }
        );
        for circuit in r.circuits() {
            if let Some(p) = &circuit.uniform {
                assert!(circuit.points.is_empty());
                assert!(p.arguments.is_empty());
                assert_eq!(p.when, Some(false));
                assert!(p.witnesses.iter().all(|w| w.epsilon_producer.is_none()));
                assert_eq!(
                    circuit.detector,
                    if body.contains("guarded") {
                        Some(Detector::Reject)
                    } else {
                        None
                    }
                );
            } else if body.contains("guarded") {
                assert_eq!(circuit.detector, Some(Detector::Reject));
                assert!(circuit.points.iter().all(|p| p.when == Some(false)));
            }
        }
    }
}
#[test]
fn missing_operand_and_unknown_guard_do_not_create_acceptance_codes() {
    for body in [
        "law required missing(c:Part):c.quantity=0;",
        "law required unknown(c:Part) when c.quantity=2:3=0;",
    ] {
        let i = inputs(body, &missing());
        let r = run(i.clone());
        assert_eq!(r.condition(), &Condition::Undetermined);
        assert!(!r.circuits().is_empty());
        assert!(r.circuits().iter().all(|c| c.detector.is_none()));
        assert!(
            r.circuits()
                .iter()
                .flat_map(|c| &c.points)
                .any(|p| p.when.is_none())
        );
        r.recheck(i, &quiet()).unwrap();
    }
}
#[test]
fn same_pattern_disagreement_retains_candidates_and_refutation_but_no_codes() {
    let r = run(inputs(
        "law required amount(c:Part):(if (forall a:Root . false) then 2 else 3)=0;",
        fixture::A,
    ));
    assert_eq!(r.condition(), &Condition::ConditionFailed);
    assert_eq!(r.circuits().len(), 2);
    assert!(r.circuits().iter().all(|c| c.detector.is_none()));
    assert!(
        r.circuits()
            .iter()
            .flat_map(|c| &c.points)
            .all(|p| p.when == Some(true))
    );
    assert!(matches!(
        r.base().outcome(),
        Some(
            archsig_computation::observed::object_law_residuals::LawResidualOutcome::Refuted { .. }
        )
    ));
}
#[test]
fn nonnumeric_original_law_is_retained_as_unsupported_and_empty_domain_is_reject() {
    let i = inputs("law required ordinary(c:Part):true;", fixture::A);
    let r = run(i.clone());
    assert_eq!(r.condition(), &Condition::Unsupported);
    assert!(r.circuits().is_empty());
    assert_eq!(r.base().evaluations().len(), 2);
    r.recheck(i, &quiet()).unwrap();
    let i = inputs(
        "law required empty(c:Part,x:(Vacant,Bool)):2=1;",
        fixture::A,
    );
    let r = run(i.clone());
    assert_eq!(r.condition(), &Condition::Ready);
    for c in r.circuits() {
        assert!(c.points.is_empty());
        assert!(c.uniform.is_none());
        assert_eq!(c.detector, Some(Detector::Reject));
    }
    r.recheck(i, &quiet()).unwrap();
}
#[test]
fn unbounded_identity_law_keeps_the_universal_circuit() {
    let i = inputs("law required infinite(c:Part,z:Z):z=z;", fixture::A);
    let r = run(Arc::clone(&i));
    assert!(r.is_complete());
    assert_eq!(r.condition(), &Condition::Ready);
    assert_eq!(r.circuits().len(), 2);
    for circuit in r.circuits() {
        assert!(circuit.points.is_empty());
        assert_eq!(circuit.detector, Some(Detector::Reject));
        assert_eq!(circuit.uniform.as_ref().unwrap().when, Some(false));
    }
    r.recheck(i, &quiet()).unwrap();
}

#[test]
fn no_laws_has_no_circuits_and_is_complete() {
    let i = inputs("view quantity(c:Part):Z=c.quantity;", fixture::A);
    let r = run(i.clone());
    assert!(r.is_complete());
    assert_eq!(r.condition(), &Condition::Ready);
    assert!(r.circuits().is_empty());
    r.recheck(i, &quiet()).unwrap();
}
#[test]
fn circuit_stops_preserve_prefix_final_completion_and_freeze_probes() {
    use archsig_common::control::Checkpoint as C;
    use archsig_input::result::Signal;
    use std::{cell::RefCell, rc::Rc};
    let i = inputs(
        "law required numeric(c:Part,b:Bool):(2,if b then 3 else 0)=(0,0);",
        fixture::A,
    );
    let baseline = run(i.clone());
    let history = Rc::new(RefCell::new(Vec::new()));
    let h = history.clone();
    let traced = Control::new(move |p| {
        h.borrow_mut().push(p);
        None
    });
    object_law_circuits(i.clone(), "Selected", "v", "root", &traced).unwrap();
    let point = C::ObjectLawCircuit;
    let count = history.borrow().iter().filter(|p| **p == point).count();
    assert!(count > 0);
    for nth in [1, count] {
        let hits = Rc::new(RefCell::new(0));
        let h = hits.clone();
        let probes = Rc::new(RefCell::new(0));
        let p = probes.clone();
        let expected = Signal::Int;
        let c = Control::new(move |at| {
            *p.borrow_mut() += 1;
            if at == point {
                *h.borrow_mut() += 1;
            }
            if at == point && *h.borrow() == nth {
                Some(Signal::Int)
            } else {
                None
            }
        });
        let f = object_law_circuits(i.clone(), "Selected", "v", "root", &c).unwrap_err();
        let ObjectLawCircuitsFailure::Reading { cause, partial } = f else {
            panic!("circuit stop")
        };
        assert_eq!(
            cause,
            archsig_computation::construction::ConstructionFailure::Stopped(expected)
        );
        assert_eq!(c.stop_reason(), Some(expected));
        assert_eq!(*hits.borrow(), nth);
        assert!(partial.base().is_complete());
        assert!(
            partial
                .circuits()
                .iter()
                .all(|c| c.complete && c.detector.is_some())
        );
        if nth == count {
            assert!(partial.is_complete());
            assert_eq!(partial.circuits(), baseline.circuits());
        }
        let before = *probes.borrow();
        assert!(c.checkpoint(C::Expression).is_err());
        assert!(c.checkpoint(C::ObjectLawCircuits).is_err());
        assert_eq!(*probes.borrow(), before);
    }
}
#[test]
fn changed_input_recheck_rejects_a_previous_detector() {
    let r = run(inputs(
        "law required amount(c:Part):c.quantity=0;",
        fixture::A,
    ));
    let changed = inputs(
        "law required amount(c:Part):c.quantity=0;",
        &fixture::A.replace("\"value\":\"2\"", "\"value\":\"0\""),
    );
    assert!(r.recheck(changed, &quiet()).is_err());
}
#[test]
fn all_missing_boolean_completion_cases_are_retained_without_accepting_a_case_selection() {
    let d = fixture::D.replace("\"type\":\"Z\"", "\"type\":\"Bool\"");
    for body in [
        "law required cases(c:Part,b:Bool):(if c.quantity then 1 else 0)=0;",
        "law required guarded(c:Part,b:Bool) when c.quantity:2=0;",
    ] {
        let i = inputs_with_definitions(&d, body, &missing());
        let r = run(i.clone());
        assert_eq!(r.condition(), &Condition::Undetermined);
        for circuit in r.circuits() {
            assert_eq!(circuit.detector, None);
            assert_eq!(circuit.points.len(), 2);
            for p in &circuit.points {
                assert_eq!(p.when, None);
                assert_eq!(p.witnesses.len(), 2);
                assert_eq!(
                    p.witnesses.iter().map(|w| w.when).collect::<Vec<_>>(),
                    [Some(false), Some(true)]
                );
                assert_ne!(
                    p.witnesses[0].original_evaluation,
                    p.witnesses[1].original_evaluation
                );
                for w in &p.witnesses {
                    assert_eq!(
                        r.base().evaluations()[w.evaluation].rows[w.row.unwrap()].cases[w.case]
                            .evaluation,
                        w.original_evaluation
                    );
                }
            }
        }
        // 再検査は guard 側の補完で代表する。
        if body.contains("guarded") {
            r.recheck(i, &quiet()).unwrap();
        }
    }
}
#[test]
fn distinct_patterns_and_q_components_keep_their_own_exact_original_reading() {
    let map=fixture::A.replace("{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}","{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"},{\"id\":\"r\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}")
        .replace("\"atoms\":[","\"atoms\":[{\"id\":\"owner-r\",\"subject\":\"r\",\"field\":\"Pattern.Part.owner\",\"value\":[\"v\",\"root\"],\"origin\":\"model\"},{\"id\":\"quantity-r\",\"subject\":\"r\",\"field\":\"Pattern.Part.quantity\",\"value\":\"5\",\"origin\":\"model\"},");
    let i = inputs(
        "view half():Q=rat(1,2);view third():Q=rat(1,3);law required mixed(c:Part):(c.quantity,half())=(2,third());",
        &map,
    );
    let r = run(i.clone());
    assert_eq!(r.condition(), &Condition::Ready);
    assert_eq!(r.base().base().profiles().classes().unwrap().len(), 3);
    assert!(r.base().comparisons().is_empty());
    let mut q = 0;
    let mut q_reject = 0;
    let mut z_accept = 0;
    let mut z_reject = 0;
    for c in r.circuits() {
        let readings = r.base().base().readings();
        let object = &readings.objects()[c.position.object]
            .identity()
            .subject()
            .subject;
        let subject = &readings.instances()[c.position.instance].bindings()[0]
            .subject()
            .subject;
        let applies = object == "root" || object == subject;
        if c.ty == archsig_common::types::Type::Q {
            if !applies {
                q_reject += 1;
                assert_eq!(c.detector, Some(Detector::Reject));
                continue;
            }
            q += 1;
            assert_eq!(c.detector, Some(Detector::Any));
            let w = &c.points[0].witnesses[0];
            let row = &r.base().evaluations()[w.evaluation].rows[w.row.unwrap()].cases[w.case];
            assert_eq!(
                row.components[1]
                    .epsilon
                    .as_ref()
                    .unwrap()
                    .wire()
                    .canonical(),
                "[\"1\",\"6\"]"
            );
        } else {
            match c.detector {
                Some(Detector::Any) => z_accept += 1,
                Some(Detector::Reject) => z_reject += 1,
                _ => panic!("Z code"),
            }
        }
    }
    assert_eq!((q, q_reject, z_accept, z_reject), (4, 2, 2, 4));
    r.recheck(i, &quiet()).unwrap();
}
