use archsig::{
    construction::{
        ConstructionFailure, construct,
        maps::{DeclarationCorrespondence, correspondence, declaration_correspondence},
        readings::object_reading_instances,
    },
    control::{Control, Limits, Usage},
    input::{CheckedInputs, InputSources, check_inputs},
    observed::{
        object_law_circuit_transport::{
            LawCircuitTransportFailureCause, LawCircuitTransportOutcome as Outcome,
            LawCircuitTransportRefutation as Refuted, ObjectLawCircuitTransport,
            ObjectLawCircuitTransportFailure, object_law_circuit_transport,
        },
        object_law_transport::LawTransportOutcome,
    },
};
use std::sync::Arc;
const D: &[u8] = include_bytes!("fixtures/object-law-family.atoms.json");
const A: &str = include_str!("fixtures/object-view-transport.archmap.json");
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn checked_inputs(law: &str, map: &str) -> Arc<CheckedInputs> {
    let right = include_bytes!("fixtures/object-law-transport-right.atoms.json");
    let defs = archsig::definition::check_definitions(&[("left", D), ("right", right)]).unwrap();
    let ld = &defs.vocabularies()["Left"].digest;
    let rd = &defs.vocabularies()["Right"].digest;
    let bridge = include_str!("fixtures/object-law-transport-bridge.atoms.json")
        .replace("@LEFT_DIGEST@", ld)
        .replace("@RIGHT_DIGEST@", rd);
    let defs = archsig::definition::check_definitions(&[
        ("left", D),
        ("right", right),
        ("bridge", bridge.as_bytes()),
    ])
    .unwrap();
    let expand = |s: &str| {
        s.replace("@LEFT_DIGEST@", ld)
            .replace("@RIGHT_DIGEST@", rd)
            .replace("@BRIDGE_DIGEST@", &defs.vocabularies()["Bridge"].digest)
            .into_bytes()
    };
    Arc::new(
        check_inputs(
            InputSources::from_bytes(
                vec![D.to_vec(), right.to_vec(), bridge.into_bytes()],
                expand(law),
                expand(map),
            ),
            &mut quiet(),
        )
        .unwrap_or_else(|f| panic!("{:?}", f.issues())),
    )
}
fn declarations(i: &CheckedInputs) -> DeclarationCorrespondence {
    let r = correspondence(i, "v", "m", "Before", Some("After"), &mut quiet()).unwrap();
    assert!(r.missing().is_empty(), "{:?}", r.missing());
    assert!(r.counterexamples().is_empty(), "{:?}", r.counterexamples());
    declaration_correspondence(i, r.map().unwrap(), &mut quiet()).unwrap()
}
fn indices(i: &CheckedInputs, object: &str, view: &str, subject: &str) -> (usize, usize) {
    let c = construct(i, "Before", "v", "a", &mut quiet()).unwrap();
    let p = object_reading_instances(i, &c, &mut quiet()).unwrap();
    (
        p.objects()
            .iter()
            .position(|o| o.identity().subject().subject == object)
            .unwrap(),
        p.instances()
            .iter()
            .position(|r| {
                r.declaration().name == format!("Before.{view}")
                    && r.bindings()
                        .iter()
                        .any(|b| b.parameter().name == "c" && b.subject().subject == subject)
            })
            .unwrap(),
    )
}

fn inputs(left: &str, right: &str, map: &str) -> Arc<CheckedInputs> {
    let uses = "use vocabulary Left version \"1\" digest \"@LEFT_DIGEST@\";use vocabulary Right version \"1\" digest \"@RIGHT_DIGEST@\";use vocabulary Bridge version \"1\" digest \"@BRIDGE_DIGEST@\";";
    checked_inputs(
        &format!(
            "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Before {{{uses}{left}}} reading After {{{uses}{right}}}"
        ),
        map,
    )
}
fn run(i: Arc<CheckedInputs>) -> ObjectLawCircuitTransport {
    let d = declarations(&i);
    let (o, n) = indices(&i, "p", "measure", "p");
    object_law_circuit_transport(i, &d, o, n, &mut quiet()).unwrap()
}
fn ground(left: &str, right: &str) -> Arc<CheckedInputs> {
    inputs(
        &format!("law required measure(c:Left.Child):{left};"),
        &format!("law required measure(d:Right.Child):{right};"),
        A,
    )
}
#[test]
fn two_false_laws_with_different_nonzero_components_refute_zero_equivalence_and_keep_operation() {
    let i = ground("(2,0)=(0,0)", "(0,3)=(0,0)");
    let r = run(i.clone());
    assert!(r.is_complete());
    assert_eq!(r.base().outcome(), &LawTransportOutcome::Preserved);
    assert!(
        matches!(r.outcome(),Outcome::Refuted(Refuted::ZeroEquivalence{component,source:true,target:false}) if component==&[0])
    );
    assert_eq!(r.points().len(), 2);
    assert_eq!(
        (r.points()[0].source_when, r.points()[0].target_when),
        (Some(true), Some(false))
    );
    assert_eq!(
        (r.points()[1].source_when, r.points()[1].target_when),
        (Some(false), Some(true))
    );
    assert!(
        r.points()
            .iter()
            .all(|p| matches!(p.outcome, Outcome::Refuted(_)))
    );
    assert_eq!(r.base().object().subject().subject, "p");
    assert_eq!(r.base().target_object().unwrap().subject().subject, "q");
    r.base().operation().recheck(&i, &mut quiet()).unwrap();
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn unequal_nonzero_values_preserve_zero_equivalence_and_detector_acceptance() {
    let i = ground("(2,0)=(0,0)", "(5,0)=(0,0)");
    let r = run(i.clone());
    assert_eq!(r.outcome(), &Outcome::Preserved);
    assert_eq!(r.points().len(), 2);
    assert_eq!(
        (r.points()[0].source_accepts, r.points()[0].target_accepts),
        (Some(true), Some(true))
    );
    assert_eq!(
        (r.points()[1].source_accepts, r.points()[1].target_accepts),
        (Some(false), Some(false))
    );
    for (side, expected) in [
        (r.source().unwrap(), "\"2\""),
        (r.target().unwrap(), "\"5\""),
    ] {
        let circuit = &side.circuits()[if expected == "\"2\"" {
            r.points()[0].source_circuit
        } else {
            r.points()[0].target_circuit
        }];
        let w = &circuit.points[0].witnesses[0];
        assert_eq!(
            side.base().evaluations()[w.evaluation].rows[w.row.unwrap()].cases[w.case].components
                [0]
            .epsilon
            .as_ref()
            .unwrap()
            .wire()
            .canonical(),
            expected
        );
    }
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn bool_fp_parameter_images_cover_all_six_arguments_and_accept_exact_nonzero_cases() {
    let i = inputs(
        "law required measure(c:Left.Child,b:Bool,f:Fp(3)):(if b then f else 0)=0;",
        "law required measure(d:Right.Child,q:Bool,g:Fp(3)):(if q then 2*g else 0)=0;",
        A,
    );
    let r = run(i.clone());
    assert_eq!(r.outcome(), &Outcome::Preserved);
    assert_eq!(r.points().len(), 6);
    for (p, (b, f)) in r.points().iter().zip([
        (false, "0"),
        (false, "1"),
        (false, "2"),
        (true, "0"),
        (true, "1"),
        (true, "2"),
    ]) {
        assert_eq!(p.source_bindings[0].0, "b");
        assert_eq!(p.target_bindings[0].0, "q");
        assert_eq!(p.source_bindings[1].0, "f");
        assert_eq!(p.target_bindings[1].0, "g");
        assert_eq!(
            p.source_bindings[0].1.wire(),
            archsig::canonical::Json::Bool(b)
        );
        assert_eq!(
            p.source_bindings[1].1.wire().canonical(),
            format!("\"{f}\"")
        );
        assert!(
            p.source_bindings
                .iter()
                .zip(&p.target_bindings)
                .all(|((_, a), (_, b))| a == b)
        );
        let accepts = b && f != "0";
        assert_eq!(
            (
                p.source_when,
                p.target_when,
                p.source_accepts,
                p.target_accepts
            ),
            (Some(accepts), Some(accepts), Some(accepts), Some(accepts))
        );
    }
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn forall_whole_false_does_not_hide_boolean_argument_component_counterexamples() {
    let i = inputs(
        "law required measure(c:Left.Child,b:Bool):(if b then 1 else 0,1)=(0,0);",
        "law required measure(d:Right.Child,q:Bool):(if q then 0 else 1,1)=(0,0);",
        A,
    );
    let r = run(i);
    assert_eq!(r.base().outcome(), &LawTransportOutcome::Preserved);
    assert!(matches!(
        r.outcome(),
        Outcome::Refuted(Refuted::ZeroEquivalence { .. })
    ));
    assert_eq!(r.points().len(), 4);
    assert_eq!(
        r.points()
            .iter()
            .filter(|p| matches!(p.outcome, Outcome::Refuted(_)))
            .count(),
        2
    );
    assert_eq!(
        r.points()
            .iter()
            .filter(|p| p.outcome == Outcome::Preserved)
            .count(),
        2
    );
}
#[test]
fn false_guards_preserve_rejection_while_unread_operands_stay_unread() {
    let i = inputs(
        "law required measure(c:Left.Child,b:Bool) when false:c.count=0;",
        "law required measure(d:Right.Child,q:Bool) when false:5=0;",
        A,
    );
    let r = run(i.clone());
    assert_eq!(r.outcome(), &Outcome::Preserved);
    assert_eq!(r.points().len(), 2);
    assert!(r.points().iter().all(|p| p.source_when == Some(false)
        && p.target_when == Some(false)
        && p.source_accepts == Some(false)
        && p.target_accepts == Some(false)));
    let source = r.source().unwrap();
    for p in r.points() {
        let witness =
            &source.circuits()[p.source_circuit].points[p.source_point.unwrap()].witnesses[0];
        let original = &source.base().evaluations()[witness.evaluation].rows[witness.row.unwrap()]
            .cases[witness.case];
        assert!(original.components[0].epsilon.is_none());
        assert!(original.components[0].left.is_none());
    }
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn role_failure_and_unknown_operand_keep_original_condition_and_operation() {
    let i = inputs(
        "law required measure(c:Left.Child):true;",
        "law optional measure(d:Right.Child):true;",
        A,
    );
    let r = run(i.clone());
    assert!(matches!(
        r.outcome(),
        Outcome::Original(LawTransportOutcome::Refuted(_))
    ));
    assert!(r.points().is_empty());
    assert!(r.source().unwrap().is_complete());
    assert!(r.target().unwrap().is_complete());
    r.base().operation().recheck(&i, &mut quiet()).unwrap();
    let missing = A
        .lines()
        .filter(|l| !l.contains("\"id\":\"p-count\""))
        .collect::<Vec<_>>()
        .join("\n");
    let i = inputs(
        "law required measure(c:Left.Child):c.count=0;",
        "law required measure(d:Right.Child):5=0;",
        &missing,
    );
    let r = run(i.clone());
    assert_eq!(
        r.outcome(),
        &Outcome::Original(LawTransportOutcome::Undetermined)
    );
    assert!(r.points().is_empty());
    r.base().operation().recheck(&i, &mut quiet()).unwrap();
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn original_nonnumeric_body_and_different_numeric_component_types_are_distinct() {
    let r = run(ground("false", "false"));
    assert!(matches!(
        r.outcome(),
        Outcome::Construction {
            source: archsig::observed::object_law_circuits::LawCircuitsCondition::Unsupported,
            target: archsig::observed::object_law_circuits::LawCircuitsCondition::Unsupported
        }
    ));
    let i = ground("2=0", "rat(1,2)=rat(0,1)");
    let r = run(i.clone());
    assert_eq!(r.base().outcome(), &LawTransportOutcome::Preserved);
    assert!(
        matches!(r.outcome(),Outcome::Refuted(Refuted::Components{source,target}) if source==&vec![(vec![],archsig::types::Type::Z)]&&target==&vec![(vec![],archsig::types::Type::Q)])
    );
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn empty_parameter_domain_preserves_vacuously_without_inventing_an_argument() {
    let i = inputs(
        "law required measure(c:Left.Child,x:(Bool,Left.Empty)):2=0;",
        "law required measure(d:Right.Child,y:(Bool,Left.Empty)):3=0;",
        A,
    );
    let r = run(i.clone());
    assert_eq!(r.outcome(), &Outcome::Preserved);
    assert!(r.points().is_empty());
    assert!(r.source().is_some());
    assert!(r.target().is_some());
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn changed_current_inputs_reject_previous_transport() {
    let r = run(ground("2=0", "3=0"));
    assert!(r.recheck(ground("2=0", "0=0"), &mut quiet()).is_err());
}
#[test]
fn fixed_stops_keep_operation_completed_prefix_refutations_final_completion_and_frozen_probes() {
    use archsig::{
        control::{Checkpoint as C, Resource, StopReason},
        result::Signal,
    };
    use std::{cell::RefCell, rc::Rc};
    let i = inputs(
        "law required measure(c:Left.Child,b:Bool):(if b then 1 else 0,1)=(0,0);",
        "law required measure(d:Right.Child,q:Bool):(if q then 0 else 1,1)=(0,0);",
        A,
    );
    let d = declarations(&i);
    let (o, n) = indices(&i, "p", "measure", "p");
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
            object_law_circuit_transport(i.clone(), &d, o, n, &mut traced).unwrap();
        }
        for at in [
            C::ObjectLawCircuitTransport,
            C::ObjectLawCircuitTransportPoint,
        ] {
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
                        object_law_circuit_transport(i.clone(), &d, o, n, &mut c).unwrap_err()
                    };
                    let ObjectLawCircuitTransportFailure::Reading {
                        cause: LawCircuitTransportFailureCause::Construction(cause),
                        partial,
                    } = f
                    else {
                        panic!("new comparison stage")
                    };
                    assert_eq!(cause, ConstructionFailure::Stopped(expected.clone()));
                    assert_eq!(c.stop_reason(), Some(expected));
                    assert_eq!(*hits.borrow(), nth);
                    assert_eq!(partial.base().object().subject().subject, "p");
                    partial
                        .base()
                        .operation()
                        .recheck(&i, &mut quiet())
                        .unwrap();
                    if at == C::ObjectLawCircuitTransportPoint {
                        assert!(!partial.points().is_empty());
                        assert!(matches!(partial.outcome(), Outcome::Refuted(_)));
                        if nth == count {
                            assert!(partial.is_complete());
                            assert_eq!(partial.points(), baseline.points());
                        }
                    }
                    if at == C::ObjectLawCircuitTransport && nth == count {
                        assert!(partial.is_complete());
                        assert_eq!(partial.points(), baseline.points());
                        assert_eq!(partial.outcome(), baseline.outcome());
                    }
                    let before = *probes.borrow();
                    assert!(c.checkpoint(C::Expression).is_err());
                    assert!(c.checkpoint(C::ObjectLawCircuitTransport).is_err());
                    assert_eq!(*probes.borrow(), before);
                }
            }
        }
    }
}
#[test]
fn source_or_target_circuit_failure_keeps_completed_other_side_and_original_operation() {
    use archsig::{control::Checkpoint as C, result::Signal};
    use std::{cell::Cell, rc::Rc};
    let i = ground("2=0", "3=0");
    let d = declarations(&i);
    let (o, n) = indices(&i, "p", "measure", "p");
    let count = Rc::new(Cell::new(0));
    let h = count.clone();
    let mut c = Control::new(Limits::default(), move |p| {
        if p == C::ObjectLawCircuits {
            h.set(h.get() + 1);
        }
        Usage::default()
    });
    object_law_circuit_transport(i.clone(), &d, o, n, &mut c).unwrap();
    let total = count.get();
    assert!(total > 1);
    for nth in [1, total] {
        let count = Rc::new(Cell::new(0));
        let h = count.clone();
        let mut c = Control::new(Limits::default(), move |p| {
            if p == C::ObjectLawCircuits {
                h.set(h.get() + 1);
            }
            Usage {
                signal: (p == C::ObjectLawCircuits && h.get() == nth).then_some(Signal::Int),
                ..Usage::default()
            }
        });
        let f = object_law_circuit_transport(i.clone(), &d, o, n, &mut c).unwrap_err();
        let ObjectLawCircuitTransportFailure::Reading { cause, partial } = f else {
            panic!("side partial")
        };
        if nth == 1 {
            assert!(matches!(cause, LawCircuitTransportFailureCause::Source(_)));
            assert!(partial.source().is_none());
        } else {
            assert!(matches!(cause, LawCircuitTransportFailureCause::Target(_)));
            assert!(partial.source().unwrap().is_complete());
        }
        assert!(partial.target().is_none());
        assert!(!partial.is_complete());
        partial
            .base()
            .operation()
            .recheck(&i, &mut quiet())
            .unwrap();
    }
}
#[test]
fn outside_instances_keep_finite_rejection_and_transport_all_actual_argument_images() {
    let i = inputs(
        "law required measure(c:Left.Child,b:Bool):2=0;",
        "law required measure(d:Right.Child,q:Bool):3=0;",
        A,
    );
    let d = declarations(&i);
    let (o, n) = indices(&i, "p", "measure", "r");
    let r = object_law_circuit_transport(i.clone(), &d, o, n, &mut quiet()).unwrap();
    assert_eq!(r.outcome(), &Outcome::Preserved);
    assert_eq!(r.points().len(), 2);
    for (j, (p, b)) in r.points().iter().zip([false, true]).enumerate() {
        assert_eq!((p.source_point, p.target_point), (Some(j), Some(j)));
        assert_eq!((p.source_when, p.target_when), (Some(false), Some(false)));
        assert_eq!(
            (p.source_accepts, p.target_accepts),
            (Some(false), Some(false))
        );
        assert_eq!(
            p.source_bindings[0].1.wire(),
            archsig::canonical::Json::Bool(b)
        );
        assert_eq!(
            p.target_bindings[0].1.wire(),
            archsig::canonical::Json::Bool(b)
        );
        for (side, circuit) in [
            (r.source().unwrap(), p.source_circuit),
            (r.target().unwrap(), p.target_circuit),
        ] {
            let circuit = &side.circuits()[circuit];
            assert!(circuit.uniform.is_none());
            assert_eq!(circuit.points.len(), 2);
            assert_eq!(circuit.points[j].arguments[0].wire(), archsig::canonical::Json::Bool(b));
            assert_eq!(circuit.points[j].when, Some(false));
            assert!(!circuit.points[j].witnesses.is_empty());
            assert!(circuit.points[j].witnesses.iter().all(|w|
                w.row == Some(j) && w.original_evaluation.is_none() && w.epsilon_producer.is_none()
            ));
        }
    }
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn a_failed_fixed_extension_keeps_its_refutation_and_does_not_generate_transport_acceptance() {
    let map = A
        .lines()
        .filter(|l| {
            !l.contains("\"id\":\"a-count\"")
                && !l.contains("\"id\":\"b-count\"")
                && !l.contains("\"id\":\"r\"")
                && !l.contains("\"id\":\"s\"")
                && !l.contains("\"subject\":\"r\"")
                && !l.contains("\"subject\":\"s\"")
        })
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",[[\"v\",\"r\"],[\"v\",\"s\"]]", "");
    let i = inputs(
        "law required measure(c:Left.Child):(if (forall a:Left.Root . false) then 2 else 3)=0;",
        "law required measure(d:Right.Child):5=0;",
        &map,
    );
    let r = run(i.clone());
    assert_eq!(r.base().outcome(), &LawTransportOutcome::Preserved);
    assert_eq!(
        r.source()
            .unwrap()
            .base()
            .base()
            .profiles()
            .classes()
            .unwrap(),
        &[vec![0, 1]]
    );
    assert!(matches!(
        r.outcome(),
        Outcome::Construction {
            source: archsig::observed::object_law_circuits::LawCircuitsCondition::ConditionFailed,
            ..
        }
    ));
    assert!(r.points().is_empty());
    assert!(matches!(
        r.source().unwrap().base().outcome(),
        Some(archsig::observed::object_law_residuals::LawResidualOutcome::Refuted { .. })
    ));
    r.base().operation().recheck(&i, &mut quiet()).unwrap();
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn unsupported_infinite_parameter_retains_the_original_failure_and_valid_operation() {
    let i = inputs(
        "law required measure(c:Left.Child,z:Z):z=z;",
        "law required measure(d:Right.Child,w:Z):w=w;",
        A,
    );
    let d = declarations(&i);
    let (o, n) = indices(&i, "p", "measure", "p");
    let f = object_law_circuit_transport(i.clone(), &d, o, n, &mut quiet()).unwrap_err();
    let ObjectLawCircuitTransportFailure::Original(
        archsig::observed::object_law_transport::ObjectLawTransportFailure::NotImplemented {
            operation, ..
        },
    ) = f
    else {
        panic!("original unsupported execution")
    };
    operation.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn option_reference_arguments_are_mapped_by_the_actual_operation_not_compared_as_labels() {
    let i = inputs(
        "law required measure(c:Left.Child,b:Option<Left.Child>):(if b=some(c) then 1 else 0)=0;",
        "law required measure(d:Right.Child,q:Option<Right.Child>):(if q=some(d) then 2 else 0)=0;",
        A,
    );
    let r = run(i.clone());
    assert_eq!(r.outcome(), &Outcome::Preserved);
    assert_eq!(r.points().len(), 3);
    let expected = [
        ("{\"none\":true}", "{\"none\":true}", false),
        ("{\"some\":[\"v\",\"p\"]}", "{\"some\":[\"v\",\"q\"]}", true),
        (
            "{\"some\":[\"v\",\"r\"]}",
            "{\"some\":[\"v\",\"s\"]}",
            false,
        ),
    ];
    for (point, (source, target, accepts)) in r.points().iter().zip(expected) {
        assert_eq!(point.source_bindings[0].1.wire().canonical(), source);
        assert_eq!(point.target_bindings[0].1.wire().canonical(), target);
        assert_eq!(
            (
                point.source_when,
                point.target_when,
                point.source_accepts,
                point.target_accepts
            ),
            (Some(accepts), Some(accepts), Some(accepts), Some(accepts))
        );
    }
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn original_holds_refutation_keeps_both_generated_numeric_circuits_and_the_operation() {
    use archsig::observed::object_law_circuits::LawCircuitDetector as Detector;
    let i = ground("2=0", "0=0");
    let r = run(i.clone());
    assert!(r.is_complete());
    assert!(matches!(
        r.outcome(),
        Outcome::Original(LawTransportOutcome::Refuted(
            archsig::observed::object_law_transport::LawConditionFailure::Holds
        ))
    ));
    assert_eq!(r.base().source_reading().unwrap().body(), Some(false));
    assert_eq!(r.base().target_reading().unwrap().body(), Some(true));
    for (side, object, instance, when, detector) in [
        (
            r.source().unwrap(),
            r.base().object(),
            r.base().instance(),
            true,
            Detector::Any,
        ),
        (
            r.target().unwrap(),
            r.base().target_object().unwrap(),
            r.base().target_instance().unwrap(),
            false,
            Detector::Reject,
        ),
    ] {
        assert!(side.is_complete());
        let readings = side.base().base().readings();
        let circuit = side
            .circuits()
            .iter()
            .find(|c| {
                readings.objects()[c.position.object].identity() == object
                    && &readings.instances()[c.position.instance] == instance
            })
            .unwrap();
        assert!(circuit.pattern.is_some());
        assert_eq!(circuit.detector, Some(detector));
        assert_eq!(circuit.points[0].when, Some(when));
        assert!(
            circuit.points[0]
                .witnesses
                .iter()
                .all(|w| w.original_evaluation.is_some() && w.epsilon_producer.is_some())
        );
    }
    assert!(r.points().is_empty());
    r.base().operation().recheck(&i, &mut quiet()).unwrap();
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn original_undetermined_keeps_unknown_source_and_known_target_circuit_evidence() {
    use archsig::observed::object_law_circuits::{
        LawCircuitDetector as Detector, LawCircuitsCondition as Condition,
    };
    let missing = A
        .lines()
        .filter(|l| !l.contains("\"id\":\"p-count\""))
        .collect::<Vec<_>>()
        .join("\n");
    let i = inputs(
        "law required measure(c:Left.Child):c.count=0;",
        "law required measure(d:Right.Child):5=0;",
        &missing,
    );
    let r = run(i.clone());
    assert!(r.is_complete());
    assert_eq!(
        r.outcome(),
        &Outcome::Original(LawTransportOutcome::Undetermined)
    );
    let source = r.source().unwrap();
    let target = r.target().unwrap();
    assert!(source.is_complete() && target.is_complete());
    assert_eq!(source.condition(), &Condition::Undetermined);
    assert_eq!(target.condition(), &Condition::Ready);
    assert!(source.circuits().iter().all(|c| c.detector.is_none()));
    assert!(
        source
            .circuits()
            .iter()
            .flat_map(|c| &c.points)
            .any(|p| p.when.is_none())
    );
    assert!(
        target
            .circuits()
            .iter()
            .any(|c| c.detector == Some(Detector::Any))
    );
    assert!(
        target
            .circuits()
            .iter()
            .flat_map(|c| &c.points)
            .flat_map(|p| &p.witnesses)
            .any(|w| w.epsilon_producer.is_some())
    );
    assert!(r.points().is_empty());
    r.base().operation().recheck(&i, &mut quiet()).unwrap();
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn side_construction_stops_retain_the_already_refuted_original_condition() {
    use archsig::{
        control::{Checkpoint as C, Resource, StopReason},
        result::Signal,
    };
    use std::{cell::Cell, rc::Rc};
    let i = ground("2=0", "0=0");
    let d = declarations(&i);
    let (o, n) = indices(&i, "p", "measure", "p");
    let baseline = run(i.clone());
    for checkpoint in [C::ObjectLawCircuitTransport, C::ObjectLawCircuits] {
        let hits = Rc::new(Cell::new(0));
        let h = hits.clone();
        let mut traced = Control::new(Limits::default(), move |p| {
            if p == checkpoint {
                h.set(h.get() + 1);
            }
            Usage::default()
        });
        object_law_circuit_transport(i.clone(), &d, o, n, &mut traced).unwrap();
        let count = hits.get();
        assert!(count > 1);
        for nth in [1, count] {
            for mode in 0..4 {
                let hits = Rc::new(Cell::new(0));
                let h = hits.clone();
                let probes = Rc::new(Cell::new(0));
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
                    move |at| {
                        p.set(p.get() + 1);
                        if at == checkpoint {
                            h.set(h.get() + 1);
                        }
                        if at == checkpoint && h.get() == nth {
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
                let f = object_law_circuit_transport(i.clone(), &d, o, n, &mut c).unwrap_err();
                let ObjectLawCircuitTransportFailure::Reading { cause, partial } = f else {
                    panic!("generation stop")
                };
                assert_eq!(partial.outcome(), baseline.outcome());
                assert!(partial.points().is_empty());
                assert_eq!(c.stop_reason(), Some(expected.clone()));
                let complete = checkpoint == C::ObjectLawCircuitTransport && nth == count;
                assert_eq!(partial.is_complete(), complete);
                if checkpoint == C::ObjectLawCircuitTransport {
                    assert!(
                        matches!(cause,LawCircuitTransportFailureCause::Construction(ConstructionFailure::Stopped(reason)) if reason==expected)
                    );
                    if complete {
                        assert!(partial.source().unwrap().is_complete());
                        assert!(partial.target().unwrap().is_complete());
                    }
                } else if nth == 1 {
                    assert!(matches!(cause, LawCircuitTransportFailureCause::Source(_)));
                } else {
                    assert!(matches!(cause, LawCircuitTransportFailureCause::Target(_)));
                    assert!(partial.source().unwrap().is_complete());
                }
                partial
                    .base()
                    .operation()
                    .recheck(&i, &mut quiet())
                    .unwrap();
                let before = probes.get();
                assert!(c.checkpoint(C::Expression).is_err());
                assert_eq!(probes.get(), before);
            }
        }
    }
}
