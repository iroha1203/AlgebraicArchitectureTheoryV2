use super::*;
use crate::observed::public_compare::{values::Data as V, Part};
mod term_fixture {
    use crate as archsig;
    include!("../../tests/common/public_term_compare.rs");
}
const PREFIX: [&str; 2] = [
    "l=evaluate(Terms.observed,s=@v/s)",
    "r=evaluate(Terms.finiteSame)",
];
const FINITE: &str = "a=compare($l.value,to=$r.value,kind=value)";
fn term_input() -> InputSources {
    term_fixture::input("", false, "term-native")
}
fn term_example(qs: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(term_input(), qs, &mut Control::unlimited()).unwrap();
    assert_eq!(r.status(), "complete", "{:?}", r.issues);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
#[test]
fn term_comparison_recheck_rejects_derived_domain_values_normalizations_and_point_forgery() {
    let r = term_example(&[
        PREFIX[0],
        PREFIX[1],
        FINITE,
        "f=evaluate(Terms.read,s=@v/s)",
        "other=evaluate(Terms.affineSlope)",
        "bad=compare($f.value,to=$other.value,kind=value)",
    ]);
    let mut variants = std::collections::BTreeSet::new();
    for (i, n) in r.nodes.iter().enumerate() {
        let Some(Payload::Construction(v)) = &n.payload else {
            continue;
        };
        let D::Comparison(Part::Derived { data, .. }) = &v.data else {
            continue;
        };
        let key = match data.as_ref() {
            V::Value { .. } => "value",
            V::Expression { .. } => "expression",
            V::Domain { .. } => "domain",
            V::Exhaustion { .. } => "exhaustion",
            V::Normalization { .. } => "normalization",
            V::Counterexample { .. } => "counterexample",
            V::Claim { .. } => "claim",
        };
        variants.insert(key);
        completion_mutation(&r, i, |nodes| {
            let Some(Payload::Construction(v)) = &mut nodes[i].payload else {
                panic!()
            };
            let D::Comparison(Part::Derived { data, .. }) = &mut v.data else {
                panic!()
            };
            match data.as_mut() {
                V::Value { value, .. } => {
                    *value = match value {
                        Scalar::Bool(b) => Scalar::Bool(!*b),
                        _ => Scalar::Bool(false),
                    }
                }
                V::Expression { left, right } => *left = *right,
                V::Domain { elements, .. } => elements.clear(),
                V::Exhaustion { checked, .. } => *checked += 1,
                V::Normalization { after, before, .. } => *after = *before,
                V::Counterexample { bindings, .. } => bindings.clear(),
                V::Claim { status, .. } => *status = Decision::Refuted,
            }
        });
        for field in 0..3 {
            completion_mutation(&r, i, |nodes| match field {
                0 => nodes[i].support.clear(),
                1 => nodes[i].scope.snapshots.clear(),
                _ => nodes[i].scope.completions = true,
            });
        }
    }
    assert_eq!(variants.len(), 7);
    let index = r.answers[2].outputs["comparison"].0;
    let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let qs = [
        PREFIX[0],
        PREFIX[1],
        "a=compare($r.value,to=$l.value,kind=value)",
        "f=evaluate(Terms.read,s=@v/s)",
        "other=evaluate(Terms.affineSlope)",
        "bad=compare($f.value,to=$other.value,kind=value)",
    ];
    for changed_source in [false, true] {
        let input = if changed_source {
            term_fixture::input("", false, "changed")
        } else {
            term_input()
        };
        let prepared = prepare_observed(input, &qs, &mut Control::unlimited()).unwrap();
        graph.requests = prepared.requests().requests().to_vec();
        let env = Environment::with_prepared(&prepared, &mut Control::unlimited()).unwrap();
        assert!(env.recheck_node(&graph, &r.nodes[index], index).is_err());
    }
}
#[test]
fn finite_and_affine_comparison_calculation_stops_keep_only_completed_derivations() {
    for (left, right, status) in [
        (PREFIX[0], PREFIX[1], Decision::Established),
        (
            "l=evaluate(Terms.read,s=@v/s)",
            "r=evaluate(Terms.affineSame)",
            Decision::Established,
        ),
        (
            "l=evaluate(Terms.read,s=@v/s)",
            "r=evaluate(Terms.affineSlope)",
            Decision::Refuted,
        ),
    ] {
        let prefix = term_example(&[left, right]);
        let prepared = prepare_observed(
            term_input(),
            &[left, right, FINITE],
            &mut Control::unlimited(),
        )
        .unwrap();
        let env = Environment::with_prepared(&prepared, &mut Control::unlimited()).unwrap();
        let graph = || {
            let mut g = rebuild_for_origin_and_support_recheck(&prefix, &prefix.nodes).unwrap();
            g.requests = prepared.requests().requests().to_vec();
            g.active = crate::observed::call::Context {
                request: 2,
                frame: None,
                iteration: None,
                instance: None,
                case: None,
            };
            g
        };
        for point in [Checkpoint::FiniteIteration, Checkpoint::Expression] {
            let count = Rc::new(Cell::new(0));
            let seen = count.clone();
            let mut probe = Control::new(Limits::default(), move |p| {
                if p == point {
                    seen.set(seen.get() + 1)
                }
                Usage::default()
            });
            let normal = crate::observed::public_compare::evaluate(
                &prepared,
                &env,
                &mut graph(),
                &prepared.requests().requests()[2],
                &mut probe,
            )
            .unwrap();
            assert_eq!(normal.status, status);
            let total = count.get();
            assert!(total > 10);
            for at in [1, total / 2, total - 1, total] {
                for mode in 0..4 {
                    let (mut c, count) = stopping(at, mode, point);
                    let mut g = graph();
                    let answer = crate::observed::public_compare::evaluate(
                        &prepared,
                        &env,
                        &mut g,
                        &prepared.requests().requests()[2],
                        &mut c,
                    );
                    match answer {
                        Ok(a) => {
                            if at == total && point == Checkpoint::FiniteIteration {
                                assert_eq!(a.status, status);
                                assert!(a.outputs.contains_key("comparison"));
                            } else if !a.outputs.contains_key("comparison") {
                                assert_eq!(a.status, Decision::Undetermined);
                            }
                            env.validate_answer(&g, &prepared.requests().requests()[2], &a)
                                .unwrap();
                            for (i, n) in g.nodes.iter().enumerate() {
                                env.recheck_node(&g, n, i).unwrap();
                            }
                        }
                        Err(ValidationFailure::Stop(_)) => {
                            assert!(at != total || point == Checkpoint::Expression)
                        }
                        Err(e) => panic!("unexpected {e:?}"),
                    }
                    assert_eq!(count.get(), at);
                    assert!(c.checkpoint(point).is_err());
                    assert_eq!(count.get(), at);
                }
            }
        }
    }
}
#[test]
fn term_comparison_transfer_stops_keep_completed_finite_and_affine_evidence() {
    for (left, right, status) in [
        (PREFIX[0], PREFIX[1], Decision::Established),
        (
            "l=evaluate(Terms.read,s=@v/s)",
            "r=evaluate(Terms.affineSlope)",
            Decision::Refuted,
        ),
    ] {
        let qs = [left, right, FINITE];
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let mut probe = Control::new(Limits::default(), move |p| {
            if p == Checkpoint::NativeResultNode {
                seen.set(seen.get() + 1)
            }
            Usage::default()
        });
        let normal = evaluate_observed_bytes(term_input(), &qs, &mut probe).unwrap();
        assert_eq!(normal.answers[2].status, status);
        let total = count.get();
        for mode in 0..4 {
            let (mut c, count) = stopping(total, mode, Checkpoint::NativeResultNode);
            let r = evaluate_observed_bytes(term_input(), &qs, &mut c).unwrap();
            assert_eq!(r.status(), "interrupted");
            assert_eq!(r.answers[2].status, status);
            assert!(r.answers[2].outputs.contains_key("comparison"));
            assert!(!r.answers[2].evidence.is_empty());
            rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
            assert_eq!(count.get(), total);
        }
    }
}
#[test]
fn term_derivation_rejects_identical_values_donated_from_another_domain_position() {
    let r = term_example(&[PREFIX[0], PREFIX[1], FINITE]);
    let values = r
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| {
            let Some(Payload::Construction(v)) = &n.payload else {
                return None;
            };
            let D::Comparison(Part::Derived { index, data }) = &v.data else {
                return None;
            };
            matches!(data.as_ref(), V::Value { .. }).then_some((i, *index, data))
        })
        .collect::<Vec<_>>();
    let (target, donor) = values
        .iter()
        .enumerate()
        .find_map(|(i, a)| values[..i].iter().find(|b| a.2 == b.2).map(|b| (*a, *b)))
        .expect("same Bool value with different domain and binding positions");
    assert_ne!(target.0, donor.0);
    completion_mutation(&r, target.0, |nodes| {
        let Some(Payload::Construction(v)) = &mut nodes[target.0].payload else {
            panic!()
        };
        let D::Comparison(Part::Derived { index, .. }) = &mut v.data else {
            panic!()
        };
        *index = donor.1;
    });
}
